-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_outer_apply
-- name    : GlobalTheory.CompanionTheory.RgEisGal.outer_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:21.646806+00:00
-- url     : https://prove2.me/theorems/f3dc1c85-8ce9-4751-9303-234a64b7a517
-- title:
--   Rg Eis Gal: outer apply
-- statement:
--   The Rg Eis Gal construction uses the outer apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StripEntireOfFac.lean#L222-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StripEntireOfFac.lean#L222-L226

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StripEntireOfFac
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal
variable {G : Type} [Group G]
variable {L W : Type} [NormedAddCommGroup L] [NormedSpace ℂ L] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [CompleteSpace W]

theorem GlobalTheory.CompanionTheory.RgEisGal.outer_apply {Γ Δ : Subgroup G} (ξ : G → ℝ) (H : ℂ → G → L →L[ℂ] W) (l : ℂ × ℂ) (g : G)
    (hs : Summable fun r : Cos Δ Γ => ‖Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g)‖)
    (w : L) : outer Γ Δ ξ H l g w =
      ∑' r : Cos Δ Γ, Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g) w := by sorry
