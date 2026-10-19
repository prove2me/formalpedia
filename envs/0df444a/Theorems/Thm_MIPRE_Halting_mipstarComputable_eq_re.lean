-- Prove2me | Theorems.Thm_MIPRE_Halting_mipstarComputable_eq_re
-- name    : MIPRE.Halting.mipstarComputable_eq_re
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:41:16.653996+00:00
-- url     : https://prove2.me/theorems/af76c716-61d4-4b88-a68d-418bb88ade24
-- title:
--   MIP* = RE for the computable class: a language has a computable family of games with gap 1 versus 1/2 if and only if it is recursively enumerable
-- statement:
--   A *language* is a set $L \subseteq \{0,1\}^*$ of bit strings; it is *recursively enumerable* ($L \in \mathrm{RE}$) when membership in $L$ is the domain of a partial computable function (Mathlib's `REPred`). Game descriptions $g = (n_X, n_A, w, \mathrm{acc})$ and the games $\mathcal{G}_g$ they describe are as in `re_subset_mipstarComputable`: two natural numbers, a list of weighted question pairs and a list of accepted answer tuples, determining a game on questions $\{0, \dots, n_X\}$ and answers $\{0, \dots, n_A\}$ with distribution $w$ normalized and exactly the listed tuples accepted, unequal answers to equal questions losing. The *quantum value* $\mathrm{val}^*(\mathcal{G})$ is the supremum, over tensor-product strategies (a unit vector $\psi \in \mathbb{C}^{d_A} \otimes \mathbb{C}^{d_B}$ and projective measurements $\{A^x_a\}$, $\{B^y_b\}$ on the factors), of $\sum_{x,y,a,b} \mu(x,y) D(x,y,a,b) \langle \psi | A^x_a \otimes B^y_b | \psi \rangle$. A language is in the *computable class* $\mathrm{MIP}^*_{\mathrm{comp}}$ when some computable map $g$ from bit strings to game descriptions sends members to games of quantum value $1$ and non-members to games of quantum value at most $\tfrac12$. The theorem states that the two classes of languages coincide:
--
--   $$ \mathrm{MIP}^*_{\mathrm{comp}} = \mathrm{RE}, \qquad\text{i.e.}\qquad \forall L \subseteq \{0,1\}^*:\ L \in \mathrm{MIP}^*_{\mathrm{comp}} \iff L \in \mathrm{RE}. $$
--
--   This is $\mathrm{MIP}^* = \mathrm{RE}$ for the class of explicit game descriptions with no time bound; `mipstar_eq_re` is the paper's-class form. Inclusions per the blueprint (`thm:mipstar-eq-re`): `re_subset_mipstarComputable` and `MIPStarComputable.isRE` (`lem:mipstar-sub-re`).
--
--   **Formalization Note**. The statement is an equality `MIPStarComputable = IsRE` of predicates on `Set BitStr`, by extensionality the pointwise equivalence displayed. `BitStr` is `List Bool`, `IsRE L := REPred (· ∈ L)` (blueprint `def:re`), and `MIPStarComputable L` (blueprint `def:mipstar-computable`) unfolds to `∃ g : BitStr → GameData, Computable g ∧ ∀ x, (x ∈ L → quantumValue (g x).game = 1) ∧ (x ∉ L → quantumValue (g x).game ≤ 1 / 2)`; `(g x).game` reads the description as a two-player `MIPRE.Game` (`GameData.game`), and `quantumValue` is the real `iSup` of the Born-rule value over tensor-product strategies. On the platform the proof is a sketch resting on the open leaf `Nonempty (MIPRE.AnswerReduction 5)`; in the repository the theorem is proved in full.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/MainTheorem.lean#L70-L71; blueprint thm:mipstar-eq-re, https://vidick.github.io/MIPRE-formalization/blueprint/; [JNVWY20] Z. Ji, A. Natarajan, T. Vidick, J. Wright, H. Yuen, MIP* = RE, arXiv:2001.04383 (2020, revised 2022)

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

theorem MIPRE.Halting.mipstarComputable_eq_re : MIPStarComputable = IsRE := by sorry
