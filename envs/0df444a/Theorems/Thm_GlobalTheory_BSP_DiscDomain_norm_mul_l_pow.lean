-- Prove2me | Theorems.Thm_GlobalTheory_BSP_DiscDomain_norm_mul_l_pow
-- name    : GlobalTheory.BSP.DiscDomain.norm_mul_l_pow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:00:33.230176+00:00
-- url     : https://prove2.me/theorems/44f8053e-4cba-42db-b148-8b3ed69335e3
-- title:
--   Disc Domain: norm mul l pow
-- statement:
--   The Disc Domain construction uses the norm mul l pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsDomainClosedDiscGaugeCompletionOfEquivNorm.lean#L50-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsDomainClosedDiscGaugeCompletionOfEquivNorm.lean#L50-L60

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

theorem GlobalTheory.BSP.DiscDomain.norm_mul_l_pow (n : ℕ) (y : PreDisc l u ρ) :
    ‖y * algebraMap A (PreDisc l u ρ) (l : A) ^ n‖ * (l : ℝ) ^ n = ‖y‖ := by sorry
