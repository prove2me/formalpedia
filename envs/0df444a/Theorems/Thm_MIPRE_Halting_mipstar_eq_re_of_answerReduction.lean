-- Prove2me | Theorems.Thm_MIPRE_Halting_mipstar_eq_re_of_answerReduction
-- name    : MIPRE.Halting.mipstar_eq_re_of_answerReduction
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:42:11.600423+00:00
-- url     : https://prove2.me/theorems/673c4023-90ce-4339-a983-8088f28c739f
-- title:
--   $\mathrm{MIP}^*_{1,1/2}(2,1) = \mathrm{RE}$ for the paper's class, given an answer reduction stage
-- statement:
--   Let $A$ be an answer reduction stage for $5$-level normal form verifiers (`MIPRE.AnswerReduction 5`). For a language $L \subseteq \{0,1\}^*$, `IsRE L` says that membership in $L$ is the domain of a partial computable function, and `MIPStar L` (blueprint `def:mipstar`, the paper's class $\mathrm{MIP}^*_{1,1/2}(2,1)$) says that some polynomial-time verifier (closed sampler and decider programs with one polynomial time bound $P$, efficient on every input $z$: sampler and decider within $P$ of the input length, overlong messages rejected) has a game $G_z$ on the strings of length at most $P(|z|)$ with quantum value $1$ when $z \in L$ and at most $\tfrac12$ when $z \notin L$. Then the two predicates on languages coincide:
--
--   $$ \mathrm{MIPStar} \;=\; \mathrm{IsRE} \qquad \text{as predicates on } \mathcal{P}(\{0,1\}^*). $$
--
--   This is blueprint `thm:mipstar-eq-re` for the paper's class, with the single remaining hypothesis an `AnswerReduction 5`: introspection, parallel repetition and the two universal machines are supplied. The inclusion $\mathrm{MIP}^*_{1,1/2}(2,1) \subseteq \mathrm{RE}$ is `MIPStar.isRE`, through the tabulation `MIPStar.toComputable` into the computable class and `MIPStarComputable.isRE`, and needs no hypothesis; the reverse inclusion is `re_subset_mipstar_of_answerReduction`.
--
--   **Formalization Note** The statement is an equality of functions `Set BitStr → Prop`, `MIPStar = IsRE`, equivalent by function and propositional extensionality to `∀ L, MIPStar L ↔ IsRE L`. `IsRE L := REPred (· ∈ L)` and `MIPStar L := ∃ V : PolyVerifier, (∀ z, V.Efficient z) ∧ ∀ z, (z ∈ L → quantumValue (V.game z) = 1) ∧ (z ∉ L → quantumValue (V.game z) ≤ 1 / 2)`, where `PolyVerifier.Efficient z` has the three clauses `sampler_runs`, `decider_time`, `rejects_long` and `V.game z` is a `Game` on `Answers (V.B z)` with `V.B z = V.bound.eval z.length`. The hypothesis `A : MIPRE.AnswerReduction 5` is an explicit argument. The source theorem `mipstar_eq_re_of` takes a `GapCompression`, a `UniversalMachine` and a `ClockedUniversalMachine`; here they are `GapCompression.ofAnswerReduction A := GapCompression.ofPipeline Introspection.seven A (repetition 7)`, `Cost.selfUniversal` and `Cost.selfClockedUniversal`. Namespace `MIPRE.Halting`, file `MIPRE/Background/Pipeline.lean`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Pipeline.lean#L102-L104

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

theorem MIPRE.Halting.mipstar_eq_re_of_answerReduction (A : MIPRE.AnswerReduction 5) : MIPStar = IsRE := by sorry
