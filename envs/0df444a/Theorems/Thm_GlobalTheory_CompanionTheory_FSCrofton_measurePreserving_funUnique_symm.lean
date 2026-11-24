-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_measurePreserving_funUnique_symm
-- name    : GlobalTheory.CompanionTheory.FSCrofton.measurePreserving_funUnique_symm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:39:20.761572+00:00
-- url     : https://prove2.me/theorems/b6c227f5-ac19-4baa-bdf8-b9c4ca4be7bb
-- title:
--   FSCrofton: measure Preserving fun Unique symm
-- statement:
--   The FSCrofton construction uses the measure Preserving fun Unique symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LintegralSplitColumn.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LintegralSplitColumn.lean#L9-L13

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralSplitColumn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton

theorem GlobalTheory.CompanionTheory.FSCrofton.measurePreserving_funUnique_symm {U : Type} [inst : Fintype U] [Unique U] :
    MeasurePreserving (MeasurableEquiv.funUnique U ℂ).symm (volume : Measure ℂ)
      (Measure.pi fun _ : U => (volume : Measure ℂ)) := by sorry
