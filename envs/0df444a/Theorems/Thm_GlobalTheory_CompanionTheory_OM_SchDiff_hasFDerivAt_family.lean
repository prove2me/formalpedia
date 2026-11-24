-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_OM_SchDiff_hasFDerivAt_family
-- name    : GlobalTheory.CompanionTheory.OM.SchDiff.hasFDerivAt_family
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:53:03.917924+00:00
-- url     : https://prove2.me/theorems/932659cc-3239-4a8a-9ed6-a5d42d5e06ed
-- title:
--   Sch Diff: has FDeriv At family
-- statement:
--   The Sch Diff construction uses the has FDeriv At family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BoundMulTranslate.lean#L123-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BoundMulTranslate.lean#L123-L150

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_ExistsHarrisTaylorObjectOfLevelLift
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoundMulTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Complex GlobalTheory.CompanionTheory.OM GlobalTheory.WeilM
open scoped ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OM GlobalTheory.CompanionTheory.OM.SchDiff
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem GlobalTheory.CompanionTheory.OM.SchDiff.hasFDerivAt_family {F : P × E → ℂ} (hF : ContDiff ℝ ∞ F) (z : P)
    (hb : ∀ k n : ℕ, ∃ C, ∀ p, ‖p - z‖ ≤ 1 → ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n F (p, x)‖ ≤ C)
    (R D : P → SchwartzMap E ℂ) (hR : ∀ p, ⇑(R p) = fun x => F (p, x))
    (hD : ∀ v, ⇑(D v) = fun x => fderiv ℝ F (z, x) (v, 0))
    (T : SchwartzMap E ℂ →L[ℂ] ℂ) (L : P →L[ℝ] ℂ) (hL : ∀ v, L v = T (D v)) :
    HasFDerivAt (fun p => T (R p)) L z := by sorry
