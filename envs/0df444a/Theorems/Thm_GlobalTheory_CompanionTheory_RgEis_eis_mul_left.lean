-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_eis_mul_left
-- name    : GlobalTheory.CompanionTheory.RgEis.eis_mul_left
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:57:17.916431+00:00
-- url     : https://prove2.me/theorems/348162da-f728-4235-86b3-c3643cf2b074
-- title:
--   Rg Eis: eis mul left
-- statement:
--   The Rg Eis construction uses the eis mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WallLawOfSectionLaw.lean#L110-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WallLawOfSectionLaw.lean#L110-L117

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

theorem GlobalTheory.CompanionTheory.RgEis.eis_mul_left (hP : IsPar Γ K P c)
    (h : ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w)
    (hη : IsHt Γ K P η) (hw : w ∈ secSp K P c ρ) (z : ℂ) {γ : G} (hγ : γ ∈ Γ) (g : G) :
    eis Γ K P c ρ (fun x => z * η x) (γ * g) w = eis Γ K P c ρ (fun x => z * η x) g w := by sorry
