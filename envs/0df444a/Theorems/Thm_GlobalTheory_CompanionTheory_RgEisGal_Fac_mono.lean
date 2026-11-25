-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_Fac_mono
-- name    : GlobalTheory.CompanionTheory.RgEisGal.Fac_mono
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:30.354851+00:00
-- url     : https://prove2.me/theorems/e0f3a178-1fdf-4225-bd9e-9a96be9d5b20
-- title:
--   Rg Eis Gal: Fac mono
-- statement:
--   The Rg Eis Gal construction uses the Fac mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DifferentiableAffLine.lean#L131-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DifferentiableAffLine.lean#L131-L134

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

theorem GlobalTheory.CompanionTheory.RgEisGal.Fac_mono {A : ℂ × ℂ → X} {Ω Ω' : Set (ℝ × ℝ)} (hA : Fac A Ω) (h : Ω' ⊆ Ω) : Fac A Ω' := by sorry
