-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_UnitaryConv_conv_comap
-- name    : GlobalTheory.CompanionTheory.RgEis.UnitaryConv.conv_comap
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:57:37.074528+00:00
-- url     : https://prove2.me/theorems/f17598df-6cd7-432f-88a8-a720ee070ed0
-- title:
--   Unitary Conv: conv comap
-- statement:
--   The Unitary Conv construction uses the conv comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnipotentConvergenceOfParabolic.lean#L37-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnipotentConvergenceOfParabolic.lean#L37-L56

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnipotentConvergenceOfParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis GlobalTheory.CompanionTheory.RgEis.UnitaryConv
open PositivityTheory.RgEis
variable {G : Type} [Group G]

theorem GlobalTheory.CompanionTheory.RgEis.UnitaryConv.conv_comap {G' : Type} [Group G'] (φ : G' →* G) {Γ P : Subgroup G} {Γ' P' : Subgroup G'} {l : G → ℝ}
    (hΓ : ∀ γ ∈ Γ', φ γ ∈ Γ) (hP : ∀ γ ∈ Γ', φ γ ∈ P → γ ∈ P')
    (hl : ∀ γ ∈ Γ, γ ∈ P → ∀ g, l (γ * g) = l g) (hc : Conv Γ P l) :
    Conv Γ' P' fun g => l (φ g) := by sorry
