-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_PhiInv_dot_pt_eq
-- name    : GlobalTheory.CompanionTheory.TubeFourier.PhiInv.dot_pt_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:33.78995+00:00
-- url     : https://prove2.me/theorems/be0cc4b9-8b81-4761-8565-59e24858d262
-- title:
--   Phi Inv: dot pt eq
-- statement:
--   The Phi Inv construction uses the dot pt eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InverseTransformRecoversFunction.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InverseTransformRecoversFunction.lean#L13-L15

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialFourierIntegralBoundStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInversionProdStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformRecoversFunction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier GlobalTheory.CompanionTheory.TubeFourier.PhiInv

theorem GlobalTheory.CompanionTheory.TubeFourier.PhiInv.dot_pt_eq (x y t : ℝ × ℝ) :
    dot (pt x y) t = ((rdot x t : ℝ) : ℂ) + Complex.I * ((rdot y t : ℝ) : ℂ) := by sorry
