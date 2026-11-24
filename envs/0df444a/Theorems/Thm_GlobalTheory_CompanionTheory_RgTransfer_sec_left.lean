-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_sec_left
-- name    : GlobalTheory.CompanionTheory.RgTransfer.sec_left
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:00:47.12463+00:00
-- url     : https://prove2.me/theorems/2a4a076e-1bf7-4da6-956a-893843b02acb
-- title:
--   Rg Transfer: sec left
-- statement:
--   The Rg Transfer construction uses the sec left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L352-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L352-L359

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

theorem GlobalTheory.CompanionTheory.RgTransfer.sec_left {ρ : K →* (W →L[ℂ] W)} (h : IsPar Γ K P c) (hs : Law K P c ρ) {w : W}
    (hw : w ∈ secSp K P c ρ) {γ : G} (hγ : γ ∈ Γ) (hγP : γ ∈ P) (x : G) :
    sec K P c ρ (γ * x) w = sec K P c ρ x w := by sorry
