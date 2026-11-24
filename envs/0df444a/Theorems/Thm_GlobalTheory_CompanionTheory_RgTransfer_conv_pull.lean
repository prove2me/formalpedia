-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_conv_pull
-- name    : GlobalTheory.CompanionTheory.RgTransfer.conv_pull
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:00:28.000923+00:00
-- url     : https://prove2.me/theorems/29be9190-b9ae-4a10-ad67-22e50c2fbb6f
-- title:
--   Rg Transfer: conv pull
-- statement:
--   The Rg Transfer construction uses the conv pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L391-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L391-L402

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

theorem GlobalTheory.CompanionTheory.RgTransfer.conv_pull (hL : IsLevi Γ K Q Γ' K' π ι c₀) (hP : IsPull Q P P' π c₀ c c') {l : G → ℝ}
    {l' : G' → ℝ} (hl : ∀ (q : Q) (k : K), l ((q : G) * k) = l' (π q))
    (hinv : ∀ γ ∈ Γ', γ ∈ P' → ∀ x, l' (γ * x) = l' x) (hc : Conv Γ' P' l') :
    Conv (Γ ⊓ Q) P l := by sorry
