-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_OM_SchDiff_bound_mul_translate
-- name    : GlobalTheory.CompanionTheory.OM.SchDiff.bound_mul_translate
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:53:22.838353+00:00
-- url     : https://prove2.me/theorems/14ec753e-80e3-4c91-b619-281dbd509647
-- title:
--   Sch Diff: bound mul translate
-- statement:
--   The Sch Diff construction uses the bound mul translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BoundMulTranslate.lean#L152-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BoundMulTranslate.lean#L152-L207

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

theorem GlobalTheory.CompanionTheory.OM.SchDiff.bound_mul_translate {A : P × E → ℂ} (hA : Function.HasTemperateGrowth A) (s : SchwartzMap E ℂ)
    (l : P →L[ℝ] E) (z : P) (k n : ℕ) :
    ∃ C, ∀ p, ‖p - z‖ ≤ 1 → ∀ x,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun q : P × E => A q * s (q.2 + l q.1)) (p, x)‖ ≤ C := by sorry
