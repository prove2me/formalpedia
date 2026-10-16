-- Prove2me | Theorems.Thm_MIPRE_Halting_re_subset_mipstarComputable
-- name    : MIPRE.Halting.re_subset_mipstarComputable
-- status  : Open
-- author  : @thomasvidick
-- created : 2026-10-15T19:41:02.663915+00:00
-- url     : https://prove2.me/theorems/5a1ae0f3-1b32-44ba-8e5a-9baef980a480
-- title:
--   RE is contained in the computable class MIP*: a computable family of games with value 1 on an r.e. language and at most 1/2 off it
-- statement:
--   A *language* is a set $L \subseteq \{0,1\}^*$ of bit strings; it is *recursively enumerable* ($L \in \mathrm{RE}$) when membership in $L$ is the domain of a partial computable function (Mathlib's `REPred`). A *game description* $g = (n_X, n_A, w, \mathrm{acc})$ consists of two natural numbers, a list $w$ of weighted question pairs and a list $\mathrm{acc}$ of accepted answer tuples; it determines a game $\mathcal{G}_g$ on questions $\{0, \dots, n_X\}$ and answers $\{0, \dots, n_A\}$ whose question distribution is $w$ normalized (a point mass at $(0,0)$ if the total weight is zero) and whose predicate accepts exactly the tuples in $\mathrm{acc}$, except that unequal answers to equal questions lose. The *quantum value* $\mathrm{val}^*(\mathcal{G})$ is the supremum, over tensor-product strategies (a unit vector $\psi \in \mathbb{C}^{d_A} \otimes \mathbb{C}^{d_B}$ and projective measurements $\{A^x_a\}$, $\{B^y_b\}$ on the factors), of $\sum_{x,y,a,b} \mu(x,y) D(x,y,a,b) \langle \psi | A^x_a \otimes B^y_b | \psi \rangle$. The theorem states that every recursively enumerable language is in the *computable class* $\mathrm{MIP}^*_{\mathrm{comp}}$: for every language $L$ with $L \in \mathrm{RE}$,
--
--   $$ \exists\, g : \{0,1\}^* \to \mathtt{GameData} \text{ computable},\quad \forall z \in \{0,1\}^*:\ \bigl(z \in L \Rightarrow \mathrm{val}^*(\mathcal{G}_{g(z)}) = 1\bigr) \ \wedge\ \bigl(z \notin L \Rightarrow \mathrm{val}^*(\mathcal{G}_{g(z)}) \le \tfrac12\bigr). $$
--
--   This is the inclusion $\mathrm{RE} \subseteq \mathrm{MIP}^*$ for the computable class, the substantive half of `mipstarComputable_eq_re`; for the class with a polynomial-time verifier the inclusion is `re_subset_mipstar`.
--
--   **Formalization Note**. `BitStr` is `List Bool`, `IsRE L := REPred (· ∈ L)` (blueprint `def:re`), and `MIPStarComputable L` (blueprint `def:mipstar-computable`) unfolds to `∃ g : BitStr → GameData, Computable g ∧ ∀ x, (x ∈ L → quantumValue (g x).game = 1) ∧ (x ∉ L → quantumValue (g x).game ≤ 1 / 2)`, with `(g x).game` the description read as a two-player `MIPRE.Game` (`GameData.game`) and `quantumValue` the real `iSup` of the Born-rule value over `MIPRE.TensorProductStrategy`. `L : Set BitStr` is an implicit argument and `h : IsRE L` the one explicit hypothesis; no polynomial-time bound on `g` is asserted. On the platform the proof is a sketch resting on the open leaf `Nonempty (MIPRE.AnswerReduction 5)`; in the repository the theorem is proved in full.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/MainTheorem.lean#L66-L67; blueprint thm:mipstar-eq-re, https://vidick.github.io/MIPRE-formalization/blueprint/; [JNVWY20] Z. Ji, A. Natarajan, T. Vidick, J. Wright, H. Yuen, MIP* = RE, arXiv:2001.04383 (2020, revised 2022)

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawInt
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_ValueApprox
import Definitions.Def_MIPRE_Foundations_ValueApprox_Cayley
import Definitions.Def_MIPRE_Foundations_ValueApprox_Projective
import Definitions.Def_MIPRE_Foundations_ValueApprox_Gaussian
import Definitions.Def_MIPRE_Foundations_ValueApprox_Norms
import Definitions.Def_MIPRE_Foundations_ValueApprox_Dense
import Definitions.Def_MIPRE_Foundations_ValueApprox_Strategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawStrategy
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawSemantics
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawComplete
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawPrimrec
import Definitions.Def_MIPRE_Foundations_ValueApprox_RE
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Semidecide
import Definitions.Def_MIPRE_Foundations_ClassMIPStarComputable
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Halting_Freeze
import Definitions.Def_MIPRE_Foundations_Halting_Classes
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Wrapper
import Definitions.Def_MIPRE_Foundations_Halting_Enumerate
import Definitions.Def_MIPRE_Foundations_ClassMIPStar
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Pipeline_AnswerReduction

open MIPRE MIPRE.Cost

theorem MIPRE.Halting.re_subset_mipstarComputable {L : Set BitStr} (h : IsRE L) : MIPStarComputable L := by sorry
