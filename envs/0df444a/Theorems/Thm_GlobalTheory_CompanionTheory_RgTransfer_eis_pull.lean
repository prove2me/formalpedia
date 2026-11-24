-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_eis_pull
-- name    : GlobalTheory.CompanionTheory.RgTransfer.eis_pull
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:00:34.076796+00:00
-- url     : https://prove2.me/theorems/35b51b69-dc03-489a-bbfc-414fef385b91
-- title:
--   Rg Transfer: eis pull
-- statement:
--   The Rg Transfer construction uses the eis pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L412-L435
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L412-L435

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

theorem GlobalTheory.CompanionTheory.RgTransfer.eis_pull (hL : IsLevi Γ K Q Γ' K' π ι c₀) (hP : IsPull Q P P' π c₀ c c')
    (hpar : IsPar Γ' K' P' c') {ρ : K →* (W →L[ℂ] W)} (h1 : Law K P c ρ)
    (h2 : Law K' P' c' (resRep hL ρ)) {Λ : G → ℂ} {Λ' : G' → ℂ}
    (hΛ : ∀ (q : Q) (k : K), Λ ((q : G) * k) = Λ' (π q))
    (hinv : ∀ γ ∈ Γ', γ ∈ P' → ∀ x, Λ' (γ * x) = Λ' x)
    {v : fixSp K Q π c₀ ρ} (hv : v ∈ secSp K' P' c' (resRep hL ρ)) (hv' : (v : W) ∈ secSp K P c ρ)
    (q : Q) (k : K)
    (hs : Summable fun y : Cos P' Γ' =>
      Complex.exp (Λ' (rep y * π q)) • sec K' P' c' (resRep hL ρ) (rep y * π q) v) :
    eis (Γ ⊓ Q) K P c ρ Λ ((q : G) * k) v = am ρ c₀ π q k (eis Γ' K' P' c' (resRep hL ρ) Λ' (π q) v) := by sorry
