-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_sec_pull
-- name    : GlobalTheory.CompanionTheory.RgTransfer.sec_pull
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:30:07.368182+00:00
-- url     : https://prove2.me/theorems/2b118196-8ce5-486a-a78e-02952f5fc01f
-- title:
--   Rg Transfer: sec pull
-- statement:
--   The Rg Transfer construction uses the sec pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L361-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L361-L385

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
variable {P : Subgroup G} {P' : Subgroup G'} {c : G → ℂ} {c' : G' → ℂ}

theorem GlobalTheory.CompanionTheory.RgTransfer.sec_pull (hL : IsLevi Γ K Q Γ' K' π ι c₀) (hP : IsPull Q P P' π c₀ c c') (hiwa : Iwa P' K')
    {ρ : K →* (W →L[ℂ] W)} (h1 : Law K P c ρ) (h2 : Law K' P' c' (resRep hL ρ))
    {v : fixSp K Q π c₀ ρ} (hv : v ∈ secSp K' P' c' (resRep hL ρ)) (hv' : (v : W) ∈ secSp K P c ρ)
    (q : Q) (k : K) :
    sec K P c ρ ((q : G) * k) v = am ρ c₀ π q k (sec K' P' c' (resRep hL ρ) (π q) v) := by sorry
