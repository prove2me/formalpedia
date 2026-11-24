-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ModDet_pi_smul_const
-- name    : GlobalTheory.CompanionTheory.SW.ModDet.pi_smul_const
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:09:26.449376+00:00
-- url     : https://prove2.me/theorems/0548631b-b3f6-42c2-93a2-c22fb324288b
-- title:
--   Mod Det: pi smul const
-- statement:
--   The Mod Det construction uses the pi smul const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MapMulVecEqSmul.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MapMulVecEqSmul.lean#L25-L30

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixTransvectionDiagonalDecompositionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarInvariantUnderTransvectionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulVecEqSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ModDet
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K]

theorem GlobalTheory.CompanionTheory.SW.ModDet.pi_smul_const {ι : Type} [Fintype ι] (lam : Measure K) [SigmaFinite lam] (c : ι → ℝ≥0) :
    Measure.pi (fun i => c i • lam) = (∏ i, c i) • Measure.pi (fun _ : ι => lam) := by sorry
