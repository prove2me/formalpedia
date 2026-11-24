-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_OM_SchDiff_taylor_iter
-- name    : GlobalTheory.CompanionTheory.OM.SchDiff.taylor_iter
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:53:34.30393+00:00
-- url     : https://prove2.me/theorems/029e9246-e3e9-4c77-83e3-61a370c39982
-- title:
--   Sch Diff: taylor iter
-- statement:
--   The Sch Diff construction uses the taylor iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BoundMulTranslate.lean#L38-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BoundMulTranslate.lean#L38-L60

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
variable {X V : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem GlobalTheory.CompanionTheory.OM.SchDiff.taylor_iter {F : X → V} (hF : ContDiff ℝ ∞ F) (n : ℕ) (a h : X) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ b ∈ segment ℝ a (a + h), ‖iteratedFDeriv ℝ (n + 2) F b‖ ≤ M) :
    ‖iteratedFDeriv ℝ n F (a + h) - iteratedFDeriv ℝ n F a
      - iteratedFDeriv ℝ n (fun b => fderiv ℝ F b h) a‖ ≤ M * ‖h‖ * ‖h‖ := by sorry
