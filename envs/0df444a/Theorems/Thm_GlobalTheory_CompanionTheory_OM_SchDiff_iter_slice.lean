-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_OM_SchDiff_iter_slice
-- name    : GlobalTheory.CompanionTheory.OM.SchDiff.iter_slice
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:53:33.977005+00:00
-- url     : https://prove2.me/theorems/ba0bf46e-94b0-4677-a1eb-c7deff50e4f5
-- title:
--   Sch Diff: iter slice
-- statement:
--   The Sch Diff construction uses the iter slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BoundMulTranslate.lean#L68-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BoundMulTranslate.lean#L68-L76

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

theorem GlobalTheory.CompanionTheory.OM.SchDiff.iter_slice {F : P × E → ℂ} (hF : ContDiff ℝ ∞ F) (n : ℕ) (p : P) (x : E) :
    iteratedFDeriv ℝ n (fun y => F (p, y)) x =
      (iteratedFDeriv ℝ n F (p, x)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ P E) := by sorry
