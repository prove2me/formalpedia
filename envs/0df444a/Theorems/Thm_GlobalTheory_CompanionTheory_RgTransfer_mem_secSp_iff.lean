-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_mem_secSp_iff
-- name    : GlobalTheory.CompanionTheory.RgTransfer.mem_secSp_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:59:26.580851+00:00
-- url     : https://prove2.me/theorems/949f615c-acba-483e-895b-72e8f4efafe3
-- title:
--   Rg Transfer: mem sec Sp iff
-- statement:
--   The Rg Transfer construction uses the mem sec Sp iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L437-L487
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L437-L487

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

theorem GlobalTheory.CompanionTheory.RgTransfer.mem_secSp_iff (hL : IsLevi Γ K Q Γ' K' π ι c₀) (hP : IsPull Q P P' π c₀ c c')
    (h1 : c' 1 = 1) (ρ : K →* (W →L[ℂ] W)) (w : W) :
    w ∈ secSp K P c ρ ↔ ∃ hw : w ∈ fixSp K Q π c₀ ρ,
      (⟨w, hw⟩ : fixSp K Q π c₀ ρ) ∈ secSp K' P' c' (resRep hL ρ) := by sorry
