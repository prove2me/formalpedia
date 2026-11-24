-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_wall_pull
-- name    : GlobalTheory.CompanionTheory.RgTransfer.wall_pull
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:01:19.563639+00:00
-- url     : https://prove2.me/theorems/0a2b2f73-2790-45f9-be2a-650481a9156c
-- title:
--   Rg Transfer: wall pull
-- statement:
--   The Rg Transfer construction uses the wall pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L606-L678
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L606-L678

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CorrESymmCoe
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgTransfer
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {G' : Type} [Group G'] [TopologicalSpace G']
variable {Γ K Q : Subgroup G} {Γ' K' : Subgroup G'} {π : Q →* G'} {ι : G' →* Q} {c₀ : G → ℂ}
variable {A A' B B' : Type} [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup A']
  [NormedSpace ℂ A'] [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup B']
  [NormedSpace ℂ B']
variable {P₁ P₂ : Subgroup G} {P₁' P₂' : Subgroup G'} {c : G → ℂ} {c' : G' → ℂ}
  {η₁ η₂ β : G → ℝ} {η₁' η₂' β' : G' → ℝ}

theorem GlobalTheory.CompanionTheory.RgTransfer.wall_pull [IsTopologicalGroup G] [LocallyCompactSpace G] [FiniteDimensional ℂ W]
    (hK : IsCompact (K : Set G)) (hL : IsLevi Γ K Q Γ' K' π ι c₀) {ρ : K →* (W →L[ℂ] W)}
    (hρ : Continuous ρ) (hP₁ : IsPull Q P₁ P₁' π c₀ c c') (hP₂ : IsPull Q P₂ P₂' π c₀ c c')
    (hpar₁ : IsPar Γ' K' P₁' c') (hpar₂ : IsPar Γ' K' P₂' c')
    (hη₁ : IsHt Γ' K' P₁' η₁') (hη₂ : IsHt Γ' K' P₂' η₂') (hβ : IsHt Γ' K' P₂' β')
    (hp₁ : PullHt K Q π η₁ η₁') (hp₂ : PullHt K Q π η₂ η₂') (hpβ : PullHt K Q π β β')
    (law₁ : Law K P₁ c ρ) (law₂ : Law K P₂ c ρ) (law₁' : Law K' P₁' c' (resRep hL ρ))
    (law₂' : Law K' P₂' c' (resRep hL ρ)) {M₁ M₂ : ℝ}
    (bd₁ : ∀ g (w : fixSp K Q π c₀ ρ), ‖sec K' P₁' c' (resRep hL ρ) g w‖ ≤ M₁ * ‖w‖)
    (bd₂ : ∀ g (w : fixSp K Q π c₀ ρ), ‖sec K' P₂' c' (resRep hL ρ) g w‖ ≤ M₂ * ‖w‖)
    {L : Submodule ℂ W} {L' : Submodule ℂ (fixSp K Q π c₀ ρ)} (hLL : Corr ρ L L')
    (hC₁ : Corr ρ (secSp K P₁ c ρ) (secSp K' P₁' c' (resRep hL ρ)))
    (hC₂ : Corr ρ (secSp K P₂ c ρ) (secSp K' P₂' c' (resRep hL ρ)))
    {R : ℝ} {D : ℂ → ℂ} {Op' : ℂ → (L' →L[ℂ] secSp K' P₂' c' (resRep hL ρ))}
    {H' : ℂ → G' → (L' →L[ℂ] fixSp K Q π c₀ ρ)}
    (hw : Wall Γ' K' P₁' P₂' c' η₁' η₂' β' (resRep hL ρ) L' R D Op' H')
    (hE : ∀ z (g : G') (k : K') (w : L'), H' z (g * k) w = resRep hL ρ k⁻¹ (H' z g w)) :
    Wall (Γ ⊓ Q) K P₁ P₂ c η₁ η₂ β ρ L R D (fun z => cj (corrE hLL) (corrE hC₂) (Op' z))
      (hOf hL ρ (corrE hLL) H') := by sorry
