-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_ext_cont
-- name    : GlobalTheory.CompanionTheory.RgTransfer.ext_cont
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:59:34.250347+00:00
-- url     : https://prove2.me/theorems/94cb9aa3-6c6d-46af-a4cc-40580583e36f
-- title:
--   Rg Transfer: ext cont
-- statement:
--   The Rg Transfer construction uses the ext cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L209-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L209-L243

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
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [IsTopologicalGroup G]

theorem GlobalTheory.CompanionTheory.RgTransfer.ext_cont {T : Type} [TopologicalSpace T] (hK : IsCompact (K : Set G))
    (hL : IsLevi Γ K Q Γ' K' π ι c₀) {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ)
    {F : T → G' → E →L[ℂ] fixSp K Q π c₀ ρ} (hF : ∀ t, Equi hL ρ (F t))
    (hc : Continuous fun y : T × G' => F y.1 y.2) :
    Continuous fun y : T × G => ext hL ρ (F y.1) y.2 := by sorry
