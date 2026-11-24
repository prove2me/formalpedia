-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_stripEntire_of_fac
-- name    : GlobalTheory.CompanionTheory.RgEisGal.stripEntire_of_fac
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:59:58.648506+00:00
-- url     : https://prove2.me/theorems/055edeaa-e568-4c53-a282-3e8c684b49f8
-- title:
--   Rg Eis Gal: strip Entire of fac
-- statement:
--   The Rg Eis Gal construction uses the strip Entire of fac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StripEntireOfFac.lean#L52-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StripEntireOfFac.lean#L52-L65

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

theorem GlobalTheory.CompanionTheory.RgEisGal.stripEntire_of_fac {f : ℂ → X} {A : ℂ × ℂ → X} (hA : Fac A Set.univ)
    (h : ∀ y, f y = A (0, y)) : StripEntire f := by sorry
