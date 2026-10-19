-- Prove2me | Theorems.Thm_MIPRE_Halting_halting_reduction_quantum_of_answerReduction
-- name    : MIPRE.Halting.halting_reduction_quantum_of_answerReduction
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:40:03.648433+00:00
-- url     : https://prove2.me/theorems/eb5c5757-8361-41a3-9eca-0dc8e09b733e
-- title:
--   Halting reduces to the quantum game value, given an answer reduction stage
-- statement:
--   Let $A$ be an answer reduction stage for $5$-level normal form verifiers (`MIPRE.AnswerReduction 5`). Programs are Mathlib's `Nat.Partrec.Code`, and a program $pc$ halts on the empty input when $pc.\mathrm{eval}\ 0$ is defined. A `GameData` is a first-order description of a synchronous game (sizes $nX, nA$, a weight list and an acceptance list); `(g\,pc).game` reads it as a two-player game of the foundations, with question set $\{0, \dots, nX\}$ for both players, answer set $\{0, \dots, nA\}$ for both, the normalized weights as distribution and the listed quadruples accepted, except that unequal answers to equal questions lose. The quantum value $\mathrm{val}^*(G) = $ `quantumValue G` (blueprint `def:q-value`) is the supremum, over all tensor-product strategies (a state $\psi \in \mathbb{C}^{d_A} \otimes \mathbb{C}^{d_B}$ and, for each player and each question, a projective measurement), of the Born-rule winning probability. Then there is a computable map $g$ from programs to game descriptions such that for every program $pc$:
--
--   $$ \bigl(pc \text{ halts on the empty input} \Rightarrow \mathrm{val}^*((g\,pc).\mathrm{game}) = 1\bigr) \;\wedge\; \bigl(pc \text{ does not halt on the empty input} \Rightarrow \mathrm{val}^*((g\,pc).\mathrm{game}) \le \tfrac12\bigr). $$
--
--   This is blueprint `cor:main-quantum`, the quantum-value form of `thm:main`, with the single remaining hypothesis an `AnswerReduction 5`: introspection, parallel repetition and the universal machine are supplied.
--
--   **Formalization Note** The statement is `∃ g : Nat.Partrec.Code → HaltingGameValue.GameData, Computable g ∧ ∀ pc, (HaltsOnEmptyInput pc → quantumValue (g pc).game = 1) ∧ (¬ HaltsOnEmptyInput pc → quantumValue (g pc).game ≤ 1 / 2)`, with `HaltsOnEmptyInput c := (c.eval 0).Dom` and `1 / 2 : ℝ`. `GameData.game g := g.syncGame.toGame` is the `MIPRE.Game (Fin (g.nX + 1)) (Fin (g.nX + 1)) (Fin (g.nA + 1)) (Fin (g.nA + 1))` with the same distribution and predicate as `toGame` (`GameData.game_μ`, `GameData.game_D`), and `MIPRE.quantumValue` is the supremum of `TensorProductStrategy.value`. The hypothesis `A : MIPRE.AnswerReduction 5` is an explicit argument. `GapCompression.ofAnswerReduction A := GapCompression.ofPipeline Introspection.seven A (repetition 7)` (same file) is the compression theorem built from the supplied introspection and repetition stages, of which this is the conditional consequence. Namespace `MIPRE.Halting`, file `MIPRE/Background/Pipeline.lean`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Pipeline.lean#L61-L66; blueprint cor:compression-from-answer-reduction

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

theorem MIPRE.Halting.halting_reduction_quantum_of_answerReduction (A : MIPRE.AnswerReduction 5) :
    ∃ g : Nat.Partrec.Code → HaltingGameValue.GameData, Computable g ∧
      ∀ pc : Nat.Partrec.Code,
        (HaltingGameValue.HaltsOnEmptyInput pc → quantumValue (g pc).game = 1) ∧
        (¬ HaltingGameValue.HaltsOnEmptyInput pc → quantumValue (g pc).game ≤ 1 / 2) := by sorry
