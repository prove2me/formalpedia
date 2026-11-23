-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_norm_term_le
-- name    : GlobalTheory.CompanionTheory.RgEis.norm_term_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:34.002916+00:00
-- url     : https://prove2.me/theorems/239691d5-6da3-4a76-a0b1-f7d3808a5b20
-- title:
--   Rg Eis: norm term le
-- statement:
--   The Rg Eis construction uses the norm term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WallLawOfSectionLaw.lean#L119-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WallLawOfSectionLaw.lean#L119-L123

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
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {η : G → ℝ} {w : W}

theorem GlobalTheory.CompanionTheory.RgEis.norm_term_le {M : ℝ} (hb : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖) {l : G → ℝ} {Λ : G → ℂ}
    (hΛ : ∀ x, (Λ x).re = l x) (x : G) (w : W) :
    ‖Complex.exp (Λ x) • sec K P c ρ x w‖ ≤ M * ‖w‖ * Real.exp (l x) := by sorry
