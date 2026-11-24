-- Prove2me | Theorems.Thm_GlobalTheory_T_summable_exp_neg_trace_totallyPositive_hermitian
-- name    : GlobalTheory.T.summable_exp_neg_trace_totallyPositive_hermitian
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:58:45.012683+00:00
-- url     : https://prove2.me/theorems/93dfe53f-c2c1-4cc0-9e05-6fce254e91cb
-- title:
--   T: summable exp neg trace totally Positive hermitian
-- statement:
--   The T construction uses the summable exp neg trace totally Positive hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableExpNegTraceTotallyPositiveHermitianStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableExpNegTraceTotallyPositiveHermitianStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableExpNegTraceTotallyPositiveHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableExpNegTraceTotallyPositiveHermitianStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.summable_exp_neg_trace_totallyPositive_hermitian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (N c : ℕ) (δ : ℝ), 0 < c → 0 < δ → Summable fun T : {T : Matrix (Fin N) (Fin N) E // ccT T = T ∧ Den c T ∧ ∀ τ : Ψ, (T.map τ.1).PosSemidef} => Real.exp (-(δ * ∑ τ : Ψ, (T.1.map τ.1).trace.re)) := by sorry
