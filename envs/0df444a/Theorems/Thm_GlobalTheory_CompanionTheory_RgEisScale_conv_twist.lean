-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisScale_conv_twist
-- name    : GlobalTheory.CompanionTheory.RgEisScale.conv_twist
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:59:42.628362+00:00
-- url     : https://prove2.me/theorems/c3b88a5c-33e4-4cd5-b154-8a0b81fcaaf9
-- title:
--   Rg Eis Scale: conv twist
-- statement:
--   The Rg Eis Scale construction uses the conv twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EisensteinScalingLaw.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EisensteinScalingLaw.lean#L25-L29

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_Descend
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EisensteinScalingLaw
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisScale
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem GlobalTheory.CompanionTheory.RgEisScale.conv_twist {Γ K P : Subgroup G} {l : G → ℝ} (hl : IsHt Γ K ⊤ l) {f f' : G → ℝ} (t : ℝ)
    (h : ∀ x, f' x = f x + t * l x) (hc : Conv Γ P f) : Conv Γ P f' := by sorry
