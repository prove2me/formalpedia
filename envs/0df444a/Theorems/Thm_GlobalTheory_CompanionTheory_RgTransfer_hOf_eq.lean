-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_hOf_eq
-- name    : GlobalTheory.CompanionTheory.RgTransfer.hOf_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:30:05.936047+00:00
-- url     : https://prove2.me/theorems/04119cbf-5f04-4690-bda5-88898089b33a
-- title:
--   Rg Transfer: h Of eq
-- statement:
--   The Rg Transfer construction uses the h Of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L589-L597
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L589-L597

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

theorem GlobalTheory.CompanionTheory.RgTransfer.hOf_eq (hL : IsLevi Γ K Q Γ' K' π ι c₀) (ρ : K →* (W →L[ℂ] W)) {L' : Type}
    [NormedAddCommGroup L'] [NormedSpace ℂ L'] (e : A ≃L[ℂ] L')
    {H' : ℂ → G' → (L' →L[ℂ] fixSp K Q π c₀ ρ)}
    (hE : ∀ z (g : G') (k : K') (w : L'), H' z (g * k) w = resRep hL ρ k⁻¹ (H' z g w))
    (z : ℂ) (q : Q) (k : K) (w : A) :
    hOf hL ρ e H' z ((q : G) * k) w = am ρ c₀ π q k (H' z (π q) (e w)) := by sorry
