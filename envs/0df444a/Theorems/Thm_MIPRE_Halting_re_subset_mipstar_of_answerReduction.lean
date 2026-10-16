-- Prove2me | Theorems.Thm_MIPRE_Halting_re_subset_mipstar_of_answerReduction
-- name    : MIPRE.Halting.re_subset_mipstar_of_answerReduction
-- status  : Open
-- author  : @thomasvidick
-- created : 2026-10-15T19:41:06.713886+00:00
-- url     : https://prove2.me/theorems/a0724274-0adf-4339-81a9-814ba280817f
-- title:
--   RE is contained in the paper's class $\mathrm{MIP}^*_{1,1/2}(2,1)$, given an answer reduction stage
-- statement:
--   Let $A$ be an answer reduction stage for $5$-level normal form verifiers (`MIPRE.AnswerReduction 5`). A language $L \subseteq \{0,1\}^*$ is recursively enumerable (`IsRE L`) when membership is the domain of a partial computable function. The class $\mathrm{MIP}^*_{1,1/2}(2,1)$ of blueprint `def:mipstar` in the paper's form (`MIPStar L`) asks for a polynomial-time verifier, a closed sampler program, a closed decider program and one polynomial $P$ with $B(z) = P(|z|)$, that is *efficient* on every input $z$ (on every seed $r$ of length $B(z)$ the sampler halts within cost $P(|z| + |r|)$ with a pair of strings of length at most $B(z)$; the decider halts within cost $P(|z| + |x| + |y| + |a| + |b|)$ on every input; and the decider rejects whenever one of $x, y, a, b$ is longer than $B(z)$) and whose game $G_z$ (questions and answers the strings of length at most $B(z)$, question pair the sampler's output on a uniform seed, decision the decider's) has quantum value $1$ when $z \in L$ and at most $\tfrac12$ when $z \notin L$. Then for every language $L$:
--
--   $$ \mathrm{IsRE}\ L \;\Longrightarrow\; \mathrm{MIPStar}\ L . $$
--
--   This is $\mathrm{RE} \subseteq \mathrm{MIP}^*_{1,1/2}(2,1)$ for the paper's class, with the single remaining hypothesis an `AnswerReduction 5`; `re_subset_mipstarComputable_of_answerReduction` is the same inclusion for the computable class.
--
--   **Formalization Note** `MIPStar L := ∃ V : PolyVerifier, (∀ z, V.Efficient z) ∧ ∀ z, (z ∈ L → quantumValue (V.game z) = 1) ∧ (z ∉ L → quantumValue (V.game z) ≤ 1 / 2)`. A randomized machine is a deterministic program with an explicit uniform seed of length $B(z)$; the decider's bound is in the total input length rather than $|z|$ alone, because a program of the ambient model reads a list only by walking it, and the paper's rejection of overlong messages is the separate clause `Efficient.rejects_long`. `V.game z` is a `Game` on `Answers (V.B z)` for questions and answers alike, with distribution `seedCount z x y / 2 ^ B z`. The hypotheses are `A : MIPRE.AnswerReduction 5` (explicit) and `h : IsRE L`, with `L` implicit. The source theorem `re_subset_mipstar_of` takes a `GapCompression`, a `UniversalMachine` and a `ClockedUniversalMachine`; here they are `GapCompression.ofAnswerReduction A := GapCompression.ofPipeline Introspection.seven A (repetition 7)`, `Cost.selfUniversal` and `Cost.selfClockedUniversal`. Namespace `MIPRE.Halting`, file `MIPRE/Background/Pipeline.lean`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Pipeline.lean#L95-L98

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

theorem MIPRE.Halting.re_subset_mipstar_of_answerReduction (A : MIPRE.AnswerReduction 5) {L : Set BitStr} (h : IsRE L) :
    MIPStar L := by sorry
