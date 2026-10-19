-- Prove2me | Theorems.Thm_MIPRE_Halting_halting_reduction_quantum
-- name    : MIPRE.Halting.halting_reduction_quantum
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:41:01.270909+00:00
-- url     : https://prove2.me/theorems/04943909-2f72-407d-a1fe-1d81bb05ac8d
-- title:
--   Halting reduces to the quantum (entangled) value of a game description
-- statement:
--   Turing machines are Mathlib's `Nat.Partrec.Code`; a code $c$ *halts on the empty input* when $\varphi_c(0)$ is defined, the empty input being encoded by $0$. A *game description* $g = (n_X, n_A, w, \mathrm{acc})$ consists of two natural numbers, a list $w$ of weighted question pairs and a list $\mathrm{acc}$ of accepted answer tuples; it determines a game $\mathcal{G}_g$ on questions $\{0, \dots, n_X\}$ and answers $\{0, \dots, n_A\}$ whose question distribution is $w$ normalized (a point mass at $(0,0)$ if the total weight is zero) and whose predicate accepts exactly the tuples in $\mathrm{acc}$, except that unequal answers to equal questions lose. The *quantum value* $\mathrm{val}^*(\mathcal{G})$ is the supremum, over tensor-product strategies (a unit vector $\psi \in \mathbb{C}^{d_A} \otimes \mathbb{C}^{d_B}$ and projective measurements $\{A^x_a\}$, $\{B^y_b\}$ on the factors), of $\sum_{x,y,a,b} \mu(x,y) D(x,y,a,b) \langle \psi | A^x_a \otimes B^y_b | \psi \rangle$. The corollary asserts
--
--   $$ \exists\, g : \mathtt{Code} \to \mathtt{GameData} \text{ computable},\quad \forall c:\ \bigl(c \text{ halts on the empty input} \Rightarrow \mathrm{val}^*(\mathcal{G}_{g(c)}) = 1\bigr) \ \wedge\ \bigl(c \text{ does not halt on the empty input} \Rightarrow \mathrm{val}^*(\mathcal{G}_{g(c)}) \le \tfrac12\bigr). $$
--
--   This is the main theorem read in the entangled value, the value in which [JNVWY20] states the reduction and the one the definition of $\mathrm{MIP}^*$ uses; the inclusion $\mathrm{RE} \subseteq \mathrm{MIP}^*$ and the uncomputability of the quantum value are stated from it.
--
--   **Formalization Note**. `(g c).game` is `HaltingGameValue.GameData.game` (`MIPRE/Foundations/GameDescription.lean`): the description read as a two-player `MIPRE.Game` on `Fin (nX + 1)` and `Fin (nA + 1)` with the same distribution and predicate as `GameData.toGame`; `MIPRE.quantumValue` is the real `iSup` over `MIPRE.TensorProductStrategy` of the Born-rule value, with the tensor product realized as a Kronecker product and the real part taken. `Computable` is Mathlib's predicate on `Nat.Partrec.Code → GameData` and `HaltsOnEmptyInput c := (c.eval 0).Dom`. The statement is its own existential: as stated, it does not identify its map with the one of `halting_reduces_to_gameValue`. On the platform the proof is a sketch resting on the open leaf `Nonempty (MIPRE.AnswerReduction 5)`; in the repository the theorem is proved in full.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/MainTheorem.lean#L44-L49; blueprint cor:main-quantum, https://vidick.github.io/MIPRE-formalization/blueprint/; [JNVWY20] Z. Ji, A. Natarajan, T. Vidick, J. Wright, H. Yuen, MIP* = RE, arXiv:2001.04383 (2020, revised 2022)

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

theorem MIPRE.Halting.halting_reduction_quantum :
    ∃ g : Nat.Partrec.Code → HaltingGameValue.GameData, Computable g ∧
      ∀ pc : Nat.Partrec.Code,
        (HaltingGameValue.HaltsOnEmptyInput pc → quantumValue (g pc).game = 1) ∧
        (¬ HaltingGameValue.HaltsOnEmptyInput pc → quantumValue (g pc).game ≤ 1 / 2) := by sorry
