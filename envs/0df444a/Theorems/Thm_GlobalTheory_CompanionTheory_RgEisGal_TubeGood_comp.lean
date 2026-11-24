-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_TubeGood_comp
-- name    : GlobalTheory.CompanionTheory.RgEisGal.TubeGood_comp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:57:14.514215+00:00
-- url     : https://prove2.me/theorems/3bd3d313-cf72-434b-b4b1-2987262d6379
-- title:
--   Rg Eis Gal: Tube Good comp
-- statement:
--   The Rg Eis Gal construction uses the Tube Good comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DifferentiableAffLine.lean#L181-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DifferentiableAffLine.lean#L181-L193

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
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
variable {E₁ E₂ E₃ : Type} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℂ E₂] [NormedAddCommGroup E₃] [NormedSpace ℂ E₃]

theorem GlobalTheory.CompanionTheory.RgEisGal.TubeGood_comp {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → E₂ →L[ℂ] E₃}
    {A : ℂ × ℂ → E₁ →L[ℂ] E₂} {Ω : Set (ℝ × ℝ)} (hF : TubeGood F Ω) (hA : Fac A Ω) :
    TubeGood (fun l g => (F l g).comp (A l)) Ω := by sorry
