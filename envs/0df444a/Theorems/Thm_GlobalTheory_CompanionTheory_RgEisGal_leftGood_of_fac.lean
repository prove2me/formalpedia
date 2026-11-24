-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_leftGood_of_fac
-- name    : GlobalTheory.CompanionTheory.RgEisGal.leftGood_of_fac
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:58:25.068903+00:00
-- url     : https://prove2.me/theorems/63fe17c4-471d-499d-900c-4f26f4e145f9
-- title:
--   Rg Eis Gal: left Good of fac
-- statement:
--   The Rg Eis Gal construction uses the left Good of fac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StripEntireOfFac.lean#L36-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StripEntireOfFac.lean#L36-L50

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
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem GlobalTheory.CompanionTheory.RgEisGal.leftGood_of_fac {f : ℂ → X} {A : ℂ × ℂ → X} {a : ℝ} (hA : Fac A {x | x.2 < a})
    (h : ∀ y, f y = A (0, y)) : LeftGood f a := by sorry
