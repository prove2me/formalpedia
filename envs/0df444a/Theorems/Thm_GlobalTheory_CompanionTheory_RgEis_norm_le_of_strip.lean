-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_norm_le_of_strip
-- name    : GlobalTheory.CompanionTheory.RgEis.norm_le_of_strip
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:57:39.415961+00:00
-- url     : https://prove2.me/theorems/f175eb03-55fd-4dab-951e-a6549b72b6fe
-- title:
--   Rg Eis: norm le of strip
-- statement:
--   The Rg Eis construction uses the norm le of strip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WallLawOfSectionLaw.lean#L53-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WallLawOfSectionLaw.lean#L53-L62

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WallLawOfSectionLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis

theorem GlobalTheory.CompanionTheory.RgEis.norm_le_of_strip {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {f : ℂ → X}
    (hf : Differentiable ℂ f) {a b B C : ℝ} (hab : a < b)
    (hB : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ B) (ha : ∀ z : ℂ, z.re = a → ‖f z‖ ≤ C)
    (hb : ∀ z : ℂ, z.re = b → ‖f z‖ ≤ C) {z : ℂ} (h1 : a ≤ z.re) (h2 : z.re ≤ b) : ‖f z‖ ≤ C := by sorry
