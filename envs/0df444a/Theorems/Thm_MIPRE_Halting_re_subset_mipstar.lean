-- Prove2me | Theorems.Thm_MIPRE_Halting_re_subset_mipstar
-- name    : MIPRE.Halting.re_subset_mipstar
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:41:00.890884+00:00
-- url     : https://prove2.me/theorems/a2525712-1f3d-40dc-9c26-b8e2cc9393c8
-- title:
--   RE is contained in MIP*_{1,1/2}(2,1): a polynomial-time verifier for every recursively enumerable language
-- statement:
--   A *language* is a set $L \subseteq \{0,1\}^*$ of bit strings; it is *recursively enumerable* ($L \in \mathrm{RE}$) when membership in $L$ is the domain of a partial computable function (Mathlib's `REPred`). The paper's class $\mathrm{MIP}^*_{1,1/2}(2,1)$: $L$ is in it when there are a sampler program $\mathcal{S}$, a decider program $\mathcal{D}$ (closed programs of the cost model) and a polynomial $P$ such that for every string $z$, with $B = P(|z|)$: on every seed $r \in \{0,1\}^B$ the sampler halts within cost $P(|z|+|r|)$ with a pair of strings of length at most $B$; on every $(z,x,y,a,b)$ the decider halts within cost $P(|z|+|x|+|y|+|a|+|b|)$, rejecting whenever one of $x,y,a,b$ is longer than $B$; and the game $\mathcal{G}_z$ (questions and answers of length at most $B$, question pair the sampler's output on a uniform $B$-bit seed, predicate the decider's acceptance) has quantum value $\mathrm{val}^*(\mathcal{G}_z) = 1$ if $z \in L$ and $\mathrm{val}^*(\mathcal{G}_z) \le \tfrac12$ if $z \notin L$, the quantum value being the supremum of the Born-rule value over tensor-product strategies. The theorem: for every language $L$,
--
--   $$ L \in \mathrm{RE} \ \Longrightarrow\ L \in \mathrm{MIP}^*_{1,1/2}(2,1). $$
--
--   This is the inclusion $\mathrm{RE} \subseteq \mathrm{MIP}^*$ for the class with a polynomial-time verifier, as [JNVWY20] states it; `re_subset_mipstarComputable` is the same inclusion for the computable class (explicit game descriptions, no time bound).
--
--   **Formalization Note**. `MIPStar L` (blueprint `def:mipstar`) unfolds to `∃ V : PolyVerifier, (∀ z, V.Efficient z) ∧ ∀ z, (z ∈ L → quantumValue (V.game z) = 1) ∧ (z ∉ L → quantumValue (V.game z) ≤ 1 / 2)`: `V` is two `WellScoped 1` programs and a `Polynomial ℕ`, `V.B z = V.bound.eval z.length`; `Efficient z` is the clauses `sampler_runs`, `decider_time` (a `HaltsWithin` bound in the total input length: a program reads a list only by walking it) and `rejects_long` (the paper's footnote); `V.game z` is a `MIPRE.Game` on `Answers (V.B z)` with $\mu_z(x,y)$ the fraction of seeds of length `B z` producing $(x,y)$ and $D_z$ = `decide (V.Accepts z x y a b)`; other sampler outputs are read as `([], [])`, a fallback never taken on an efficient verifier. `L : Set BitStr` is implicit and `h : IsRE L` (`IsRE L := REPred (· ∈ L)`) the one hypothesis. On the platform the proof is a sketch resting on the open leaf `Nonempty (MIPRE.AnswerReduction 5)`; in the repository the theorem is proved in full.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/MainTheorem.lean#L74-L75; blueprint thm:mipstar-eq-re, https://vidick.github.io/MIPRE-formalization/blueprint/; [JNVWY20] Z. Ji, A. Natarajan, T. Vidick, J. Wright, H. Yuen, MIP* = RE, arXiv:2001.04383 (2020, revised 2022)

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

theorem MIPRE.Halting.re_subset_mipstar {L : Set BitStr} (h : IsRE L) : MIPStar L := by sorry
