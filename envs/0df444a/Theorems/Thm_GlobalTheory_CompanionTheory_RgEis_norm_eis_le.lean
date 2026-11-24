-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_norm_eis_le
-- name    : GlobalTheory.CompanionTheory.RgEis.norm_eis_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:57:45.828037+00:00
-- url     : https://prove2.me/theorems/bd5f9aeb-9cac-4b4b-9871-c4941bc8a7e2
-- title:
--   Rg Eis: norm eis le
-- statement:
--   The Rg Eis construction uses the norm eis le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WallLawOfSectionLaw.lean#L130-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WallLawOfSectionLaw.lean#L130-L133

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

theorem GlobalTheory.CompanionTheory.RgEis.norm_eis_le {M : ℝ} (hb : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖) {l : G → ℝ}
    (hl : Conv Γ P l) {Λ : G → ℂ} (hΛ : ∀ x, (Λ x).re = l x) (g : G) (w : W) :
    ‖eis Γ K P c ρ Λ g w‖ ≤ M * ‖w‖ * pos Γ P l g := by sorry
