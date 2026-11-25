-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ParSmooth_continuous_iteratedFDeriv_partial
-- name    : GlobalTheory.CompanionTheory.ParSmooth.continuous_iteratedFDeriv_partial
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:58:11.330996+00:00
-- url     : https://prove2.me/theorems/9b033539-ba12-4a56-9b43-4438ad5a394a
-- title:
--   Par Smooth: continuous iterated FDeriv partial
-- statement:
--   The Par Smooth construction uses the continuous iterated FDeriv partial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/JetProofs/ContinuousIteratedFDerivPartial.lean#L9-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/JetProofs/ContinuousIteratedFDerivPartial.lean#L9-L28

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_JetProofs_ContinuousIteratedFDerivPartial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ParSmooth

theorem GlobalTheory.CompanionTheory.ParSmooth.continuous_iteratedFDeriv_partial {P Q E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ψ : P × Q → E) (hΨ : ContDiff ℝ ∞ Ψ) (k : ℕ) :
    Continuous fun z : P × Q => iteratedFDeriv ℝ k (fun y => Ψ (y, z.2)) z.1 := by sorry
