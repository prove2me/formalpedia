-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_eis_mul_right
-- name    : GlobalTheory.CompanionTheory.RgEis.eis_mul_right
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:57:32.560189+00:00
-- url     : https://prove2.me/theorems/8ae53c26-f346-4c7e-ac3d-1647958cb80f
-- title:
--   Rg Eis: eis mul right
-- statement:
--   The Rg Eis construction uses the eis mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WallLawOfSectionLaw.lean#L138-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WallLawOfSectionLaw.lean#L138-L150

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

theorem GlobalTheory.CompanionTheory.RgEis.eis_mul_right [CompleteSpace W] (hP : IsPar Γ K P c)
    (h : ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w)
    {M : ℝ} (hb : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖)
    (hη : IsHt Γ K P η) (hw : w ∈ secSp K P c ρ) (z : ℂ) (hc : Conv Γ P fun g => z.re * η g) (g : G) (k : K) :
    eis Γ K P c ρ (fun x => z * η x) (g * k) w = ρ k⁻¹ (eis Γ K P c ρ (fun x => z * η x) g w) := by sorry
