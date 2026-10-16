-- Prove2me | Theorems.Thm_MIPRE_Halting_mipstar_eq_re
-- name    : MIPRE.Halting.mipstar_eq_re
-- status  : Open
-- author  : @thomasvidick
-- created : 2026-10-15T19:42:41.950147+00:00
-- url     : https://prove2.me/theorems/91337971-2705-496b-8c51-616ba7c648bb
-- title:
--   MIP*_{1,1/2}(2,1) = RE: the title theorem of MIP* = RE, for the paper's class
-- statement:
--   A *language* is a set $L \subseteq \{0,1\}^*$ of bit strings; it is *recursively enumerable* ($L \in \mathrm{RE}$) when membership in $L$ is the domain of a partial computable function (Mathlib's `REPred`). The paper's class $\mathrm{MIP}^*_{1,1/2}(2,1)$: $L$ is in it when there are a sampler program $\mathcal{S}$, a decider program $\mathcal{D}$ (closed programs of the cost model) and a polynomial $P$ such that for every string $z$, with $B = P(|z|)$: on every seed $r \in \{0,1\}^B$ the sampler halts within cost $P(|z|+|r|)$ with a pair of strings of length at most $B$; on every $(z,x,y,a,b)$ the decider halts within cost $P(|z|+|x|+|y|+|a|+|b|)$, rejecting whenever one of $x,y,a,b$ is longer than $B$; and the game $\mathcal{G}_z$ (questions and answers of length at most $B$, question pair the sampler's output on a uniform $B$-bit seed, predicate the decider's acceptance) has quantum value $\mathrm{val}^*(\mathcal{G}_z) = 1$ if $z \in L$ and $\mathrm{val}^*(\mathcal{G}_z) \le \tfrac12$ if $z \notin L$, the quantum value being the supremum of the Born-rule value over tensor-product strategies. The theorem states that the two classes of languages coincide:
--
--   $$ \mathrm{MIP}^*_{1,1/2}(2,1) = \mathrm{RE}, \qquad\text{i.e.}\qquad \forall L \subseteq \{0,1\}^*:\ L \in \mathrm{MIP}^*_{1,1/2}(2,1) \iff L \in \mathrm{RE}. $$
--
--   This is the title equality of [JNVWY20]; `mipstarComputable_eq_re` is its computable-class form. Inclusions per the blueprint (`thm:mipstar-eq-re`): `re_subset_mipstar` and `lem:mipstar-poly-sub` (`MIPStar.isRE`).
--
--   **Formalization Note**. The statement is an equality `MIPStar = IsRE` of predicates on `Set BitStr`, by extensionality the pointwise equivalence displayed; `BitStr` is `List Bool` and `IsRE L := REPred (· ∈ L)`. `MIPStar L` (blueprint `def:mipstar`) unfolds to `∃ V : PolyVerifier, (∀ z, V.Efficient z) ∧ ∀ z, (z ∈ L → quantumValue (V.game z) = 1) ∧ (z ∉ L → quantumValue (V.game z) ≤ 1 / 2)`, with `PolyVerifier`, `Efficient` (clauses `sampler_runs`, `decider_time`, `rejects_long`; the time bounds are `HaltsWithin` bounds of the cost model in the total input length) and `V.game z` (a `MIPRE.Game` on `Answers (V.B z)`; a sampler output that is not a pair of strings of length at most `B z` is read as `([], [])`, a fallback never taken on an efficient verifier) as in `re_subset_mipstar`. On the platform the proof is a sketch resting on the open leaf `Nonempty (MIPRE.AnswerReduction 5)`; in the repository the theorem is proved in full.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/MainTheorem.lean#L78-L79; blueprint thm:mipstar-eq-re, https://vidick.github.io/MIPRE-formalization/blueprint/; [JNVWY20] Z. Ji, A. Natarajan, T. Vidick, J. Wright, H. Yuen, MIP* = RE, arXiv:2001.04383 (2020, revised 2022)

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

theorem MIPRE.Halting.mipstar_eq_re : MIPStar = IsRE := by sorry
