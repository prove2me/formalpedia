-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_am_apply
-- name    : GlobalTheory.CompanionTheory.RgTransfer.am_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:45.85974+00:00
-- url     : https://prove2.me/theorems/d12be97d-1996-46cf-84b4-8eb0feb03865
-- title:
--   Rg Transfer: am apply
-- statement:
--   The Rg Transfer construction uses the am apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L109-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L109-L110

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

theorem GlobalTheory.CompanionTheory.RgTransfer.am_apply (ρ : K →* (W →L[ℂ] W)) (q : Q) (k : K) (v : fixSp K Q π c₀ ρ) :
    am ρ c₀ π q k v = c₀ q • ρ k⁻¹ (v : W) := by sorry
