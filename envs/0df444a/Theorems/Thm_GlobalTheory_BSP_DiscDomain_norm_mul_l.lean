-- Prove2me | Theorems.Thm_GlobalTheory_BSP_DiscDomain_norm_mul_l
-- name    : GlobalTheory.BSP.DiscDomain.norm_mul_l
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:00:45.904529+00:00
-- url     : https://prove2.me/theorems/449cbf29-74b0-4ea6-a365-4f5f4d4d843b
-- title:
--   Disc Domain: norm mul l
-- statement:
--   The Disc Domain construction uses the norm mul l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsDomainClosedDiscGaugeCompletionOfEquivNorm.lean#L37-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsDomainClosedDiscGaugeCompletionOfEquivNorm.lean#L37-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemBallOfGaugeLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsDomainClosedDiscGaugeCompletionOfEquivNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory GlobalTheory.BSP GlobalTheory.BSP.DiscDomain
variable {l : ℕ} [hl : Fact l.Prime] {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0}

theorem GlobalTheory.BSP.DiscDomain.norm_mul_l (y : PreDisc l u ρ) :
    ‖y * algebraMap A (PreDisc l u ρ) (l : A)‖ * l = ‖y‖ := by sorry
