-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_am_bound
-- name    : GlobalTheory.CompanionTheory.RgTransfer.am_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:00:21.486405+00:00
-- url     : https://prove2.me/theorems/81a1563d-ab82-4825-a2c4-e420e53e3f40
-- title:
--   Rg Transfer: am bound
-- statement:
--   The Rg Transfer construction uses the am bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L245-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L245-L254

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

theorem GlobalTheory.CompanionTheory.RgTransfer.am_bound (hK : IsCompact (K : Set G)) (hL : IsLevi Γ K Q Γ' K' π ι c₀)
    {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ) : ∃ B : ℝ, ∀ (q : Q) (k : K), ‖am ρ c₀ π q k‖ ≤ B := by sorry
