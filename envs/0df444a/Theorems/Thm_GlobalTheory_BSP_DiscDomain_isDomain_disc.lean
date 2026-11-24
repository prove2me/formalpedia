-- Prove2me | Theorems.Thm_GlobalTheory_BSP_DiscDomain_isDomain_disc
-- name    : GlobalTheory.BSP.DiscDomain.isDomain_disc
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:00:27.671947+00:00
-- url     : https://prove2.me/theorems/b67cef05-372d-491e-b560-6e67356c6e9e
-- title:
--   Disc Domain: is Domain disc
-- statement:
--   The Disc Domain construction uses the is Domain disc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsDomainClosedDiscGaugeCompletionOfEquivNorm.lean#L96-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsDomainClosedDiscGaugeCompletionOfEquivNorm.lean#L96-L123

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

theorem GlobalTheory.BSP.DiscDomain.isDomain_disc (l : ℕ) [hl : Fact l.Prime] (A : Type) [CommRing A] (u : A) (ρ : ℝ≥0) (N : A → ℝ) (c : ℝ)
    (hc : 0 < c) (hmul : ∀ x y, N (x * y) = N x * N y) (_hadd : ∀ x y, N (x + y) ≤ max (N x) (N y))
    (hNl : N (l : A) = (l : ℝ)⁻¹) (hle : ∀ x, N x ≤ ‖toDisc l u ρ x‖) (hge : ∀ x, c * ‖toDisc l u ρ x‖ ≤ N x) :
    IsDomain (Disc l u ρ) ∧ ∀ x y : Disc l u ρ, c ^ 2 * (‖x‖ * ‖y‖) ≤ ‖x * y‖ := by sorry
