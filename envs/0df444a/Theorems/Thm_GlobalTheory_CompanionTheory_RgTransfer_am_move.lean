-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_am_move
-- name    : GlobalTheory.CompanionTheory.RgTransfer.am_move
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:59:55.539303+00:00
-- url     : https://prove2.me/theorems/69825f9b-b388-426c-b4f9-4a17adbfe814
-- title:
--   Rg Transfer: am move
-- statement:
--   The Rg Transfer construction uses the am move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L112-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L112-L145

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

theorem GlobalTheory.CompanionTheory.RgTransfer.am_move (hL : IsLevi Γ K Q Γ' K' π ι c₀) (ρ : K →* (W →L[ℂ] W)) (q : Q) (k r : K)
    (hr : (r : G) ∈ Q) (v : fixSp K Q π c₀ ρ) :
    am ρ c₀ π (q * ⟨r, hr⟩) (r⁻¹ * k)
      (resRep hL ρ ⟨π ⟨r, hr⟩, hL.πK ⟨r, hr⟩ r.2⟩⁻¹ v) = am ρ c₀ π q k v := by sorry
