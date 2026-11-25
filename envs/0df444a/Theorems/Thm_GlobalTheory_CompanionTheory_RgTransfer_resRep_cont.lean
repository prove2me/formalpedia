-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_resRep_cont
-- name    : GlobalTheory.CompanionTheory.RgTransfer.resRep_cont
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:00:02.748255+00:00
-- url     : https://prove2.me/theorems/76b16a0c-a37a-41da-b8e9-b1e3a26a3222
-- title:
--   Rg Transfer: res Rep cont
-- statement:
--   The Rg Transfer construction uses the res Rep cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L97-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L97-L104

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

theorem GlobalTheory.CompanionTheory.RgTransfer.resRep_cont [FiniteDimensional ℂ W] (hL : IsLevi Γ K Q Γ' K' π ι c₀)
    {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ) : Continuous (resRep hL ρ) := by sorry
