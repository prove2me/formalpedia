-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_TubeGood_mono
-- name    : GlobalTheory.CompanionTheory.RgEisGal.TubeGood_mono
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:57:27.479822+00:00
-- url     : https://prove2.me/theorems/3b8cfcea-aec5-45ac-ac7d-93967b10a555
-- title:
--   Rg Eis Gal: Tube Good mono
-- statement:
--   The Rg Eis Gal construction uses the Tube Good mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DifferentiableAffLine.lean#L83-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DifferentiableAffLine.lean#L83-L88

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
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem GlobalTheory.CompanionTheory.RgEisGal.TubeGood_mono {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω Ω' : Set (ℝ × ℝ)}
    (hF : TubeGood F Ω) (h : Ω' ⊆ Ω) : TubeGood F Ω' := by sorry
