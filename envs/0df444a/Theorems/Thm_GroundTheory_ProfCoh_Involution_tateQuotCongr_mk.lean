-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_Involution_tateQuotCongr_mk
-- name    : GroundTheory.ProfCoh.Involution.tateQuotCongr_mk
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:11:12.635435+00:00
-- url     : https://prove2.me/theorems/fb05345b-42df-48e0-bf11-00a4ab019ab7
-- title:
--   Involution: tate Quot Congr mk
-- statement:
--   The Involution construction uses the tate Quot Congr mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RealPlaces/InvolutionDuality.lean#L202-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RealPlaces/InvolutionDuality.lean#L202-L205

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualFinite
import Definitions.Def_GroundTheory_ProfiniteCohomology_RealPlaces_InvolutionDuality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.ProfCoh.Involution
variable {M : Type*} [AddCommGroup M]
variable {σ : M →+ M}
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

theorem GroundTheory.ProfCoh.Involution.tateQuotCongr_mk (e : M ≃+ N) {σ : M →+ M} {τ : N →+ N} (he : ∀ x, e (σ x) = τ (e x))
    (x : fixedSub σ) :
    tateQuotCongr e he (x : tateQuot σ) = (fixedSubCongr e he x : tateQuot τ) := by sorry

attribute [defeq] GroundTheory.ProfCoh.Involution.tateQuotCongr_mk
