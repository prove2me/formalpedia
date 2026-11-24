-- Prove2me | Theorems.Thm_GlobalTheory_ConeImage_isClosed_cone
-- name    : GlobalTheory.ConeImage.isClosed_cone
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:25:26.189929+00:00
-- url     : https://prove2.me/theorems/841c19a2-7269-473e-9199-7b5a267c72fe
-- title:
--   Cone Image: is Closed cone
-- statement:
--   The Cone Image construction uses the is Closed cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsNhdsSubsetRange.lean#L61-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsNhdsSubsetRange.lean#L61-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsNhdsSubsetRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ConeImage

theorem GlobalTheory.ConeImage.isClosed_cone {E ι : Type*} [TopologicalSpace E] {f : E → ι → ℂ} (hf : Continuous f)
    (h0 : ∀ z, f z ≠ 0) {K : Set E} (hK : IsCompact K) :
    IsClosed {p : ι → ℂ | ∃ t : ℂ, ∃ z ∈ K, p = t • f z} := by sorry
