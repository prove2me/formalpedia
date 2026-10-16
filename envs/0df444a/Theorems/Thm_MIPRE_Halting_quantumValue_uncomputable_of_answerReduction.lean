-- Prove2me | Theorems.Thm_MIPRE_Halting_quantumValue_uncomputable_of_answerReduction
-- name    : MIPRE.Halting.quantumValue_uncomputable_of_answerReduction
-- status  : Open
-- author  : @thomasvidick
-- created : 2026-10-15T19:40:14.456205+00:00
-- url     : https://prove2.me/theorems/d9227116-1b6b-4bc8-bd71-026f080100b1
-- title:
--   The quantum game value is uncomputable, given an answer reduction stage
-- statement:
--   Let $A$ be an answer reduction stage for $5$-level normal form verifiers (`MIPRE.AnswerReduction 5`). A `GameData` $d$ is a first-order description of a synchronous game (sizes $nX, nA$, a weight list and an acceptance list), `d.game` its reading as a two-player game of the foundations on questions $\{0, \dots, nX\}$ and answers $\{0, \dots, nA\}$ for both players, and $\mathrm{val}^*(d.\mathrm{game}) = $ `quantumValue d.game` its quantum value, the supremum of the Born-rule winning probability over tensor-product strategies (a bipartite state and a projective measurement for each player and question). The theorem says that no computable Boolean function decides the promise problem "quantum value $1$ versus quantum value at most $\tfrac12$":
--
--   $$ \neg\,\exists\, f : \mathtt{GameData} \to \mathrm{Bool},\ \mathrm{Computable}\, f \;\wedge\; \bigl(\forall d,\ \mathrm{val}^*(d.\mathrm{game}) = 1 \Rightarrow f\,d = \mathtt{true}\bigr) \;\wedge\; \bigl(\forall d,\ \mathrm{val}^*(d.\mathrm{game}) \le \tfrac12 \Rightarrow f\,d = \mathtt{false}\bigr). $$
--
--   Nothing is required of $f$ on descriptions whose value lies strictly between $\tfrac12$ and $1$. This is the second clause of blueprint `cor:value-uncomputable`, with the single remaining hypothesis an `AnswerReduction 5`; the first clause, for the synchronous value, is `gameValue_uncomputable_of_answerReduction`.
--
--   **Formalization Note** The statement is exactly `¬ ∃ f : HaltingGameValue.GameData → Bool, Computable f ∧ (∀ d, quantumValue d.game = 1 → f d = true) ∧ (∀ d, quantumValue d.game ≤ 1 / 2 → f d = false)`, with `GameData.game g := g.syncGame.toGame` the `MIPRE.Game` with the distribution and predicate of `toGame`, `MIPRE.quantumValue` the supremum of `TensorProductStrategy.value`, `Computable` Mathlib's (relative to the `Primcodable` instance of `GameData`) and `1 / 2 : ℝ`. The hypothesis `A : MIPRE.AnswerReduction 5` is an explicit argument. `GapCompression.ofAnswerReduction A := GapCompression.ofPipeline Introspection.seven A (repetition 7)` (same file) is the compression theorem built from the supplied introspection and repetition stages, of which this is the conditional consequence. Namespace `MIPRE.Halting`, file `MIPRE/Background/Pipeline.lean`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Pipeline.lean#L78-L82; blueprint cor:compression-from-answer-reduction

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

theorem MIPRE.Halting.quantumValue_uncomputable_of_answerReduction (A : MIPRE.AnswerReduction 5) :
    ¬ ∃ f : HaltingGameValue.GameData → Bool, Computable f ∧
      (∀ d, quantumValue d.game = 1 → f d = true) ∧
      (∀ d, quantumValue d.game ≤ 1 / 2 → f d = false) := by sorry
