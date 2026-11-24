-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_ext_bdd
-- name    : GlobalTheory.CompanionTheory.RgTransfer.ext_bdd
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:59:19.967331+00:00
-- url     : https://prove2.me/theorems/c8f4bf24-716c-4814-83d3-129f2eb614ca
-- title:
--   Rg Transfer: ext bdd
-- statement:
--   The Rg Transfer construction uses the ext bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L256-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L256-L292

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

theorem GlobalTheory.CompanionTheory.RgTransfer.ext_bdd [LocallyCompactSpace G] {T : Type} (hK : IsCompact (K : Set G))
    (hL : IsLevi Γ K Q Γ' K' π ι c₀) {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ) (S : Set T)
    (F : T → G' → E →L[ℂ] fixSp K Q π c₀ ρ)
    (hb : ∀ g', ∃ U ∈ 𝓝 g', ∃ M : ℝ, ∀ t ∈ S, ∀ x ∈ U, ‖F t x‖ ≤ M) (g : G) :
    ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ t ∈ S, ∀ g' ∈ U, ‖ext hL ρ (F t) g'‖ ≤ M := by sorry
