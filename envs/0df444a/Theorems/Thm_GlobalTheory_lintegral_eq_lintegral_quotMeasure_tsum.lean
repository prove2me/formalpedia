-- Prove2me | Theorems.Thm_GlobalTheory_lintegral_eq_lintegral_quotMeasure_tsum
-- name    : GlobalTheory.lintegral_eq_lintegral_quotMeasure_tsum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:35.27418+00:00
-- url     : https://prove2.me/theorems/6b196168-0a1c-451c-9d2e-b42b643dfe67
-- title:
--   Global Theory: lintegral eq lintegral quot Measure tsum
-- statement:
--   The Global Theory construction uses the lintegral eq lintegral quot Measure tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L442-L455
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L442-L455

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Topology Filter
open scoped Pointwise ENNReal
open GlobalTheory
variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}
variable [Countable G] [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ]

theorem GlobalTheory.lintegral_eq_lintegral_quotMeasure_tsum [h : HasFundamentalDomain G X μ] {f : X → ℝ≥0∞}
    (hf : Measurable f) {F : Quotient (MulAction.orbitRel G X) → ℝ≥0∞}
    (hF : ∀ x, F (Quotient.mk _ x) = ∑' g : G, f (g • x)) :
    ∫⁻ x, f x ∂μ = ∫⁻ q, F q ∂quotMeasure G μ := by sorry
