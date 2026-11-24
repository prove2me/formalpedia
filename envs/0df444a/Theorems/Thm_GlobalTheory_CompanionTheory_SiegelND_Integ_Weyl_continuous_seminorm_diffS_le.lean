-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Weyl_continuous_seminorm_diffS_le
-- name    : GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.continuous_seminorm_diffS_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:13:53.007802+00:00
-- url     : https://prove2.me/theorems/6a918a1b-29e7-4c8d-b915-fe3bc6aef501
-- title:
--   Weyl: continuous seminorm diff S le
-- statement:
--   The Weyl construction uses the continuous seminorm diff S le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousSeminormDiffSLe.lean#L111-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousSeminormDiffSLe.lean#L111-L128

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

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.continuous_seminorm_diffS_le (f : SchwartzMap V ℂ) (K : ℕ)
    (p : Seminorm ℂ (SchwartzMap V ℂ)) (hp : Continuous p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : V, p (diffS f y) ≤ C * ((1 + ‖y‖) ^ K)⁻¹ := by sorry
