-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Weyl_seminorm_diffS_le
-- name    : GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.seminorm_diffS_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:15:48.279859+00:00
-- url     : https://prove2.me/theorems/53bb134f-1510-4596-9436-159d2757203d
-- title:
--   Weyl: seminorm diff S le
-- statement:
--   The Weyl construction uses the seminorm diff S le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousSeminormDiffSLe.lean#L101-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousSeminormDiffSLe.lean#L101-L109

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousSeminormDiffSLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
open MeasureTheory
open scoped ComplexConjugate FourierTransform
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.seminorm_diffS_le (f : SchwartzMap V ℂ) (k n K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : V,
      SchwartzMap.seminorm ℂ k n (diffS f y) ≤ C * ((1 + ‖y‖) ^ K)⁻¹ := by sorry
