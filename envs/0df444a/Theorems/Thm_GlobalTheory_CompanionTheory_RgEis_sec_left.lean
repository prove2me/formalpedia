-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_sec_left
-- name    : GlobalTheory.CompanionTheory.RgEis.sec_left
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:57:09.03581+00:00
-- url     : https://prove2.me/theorems/82bbb70f-0adb-4283-8ded-10093978c8ae
-- title:
--   Rg Eis: sec left
-- statement:
--   The Rg Eis construction uses the sec left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WallLawOfSectionLaw.lean#L88-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WallLawOfSectionLaw.lean#L88-L96

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

theorem GlobalTheory.CompanionTheory.RgEis.sec_left (hP : IsPar Γ K P c)
    (h : ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w)
    (hw : w ∈ secSp K P c ρ) {δ : G} (h1 : δ ∈ Γ) (h2 : δ ∈ P) (x : G) :
    sec K P c ρ (δ * x) w = sec K P c ρ x w := by sorry
