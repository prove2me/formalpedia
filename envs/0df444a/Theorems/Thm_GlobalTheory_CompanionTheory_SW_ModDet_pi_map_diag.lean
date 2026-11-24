-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ModDet_pi_map_diag
-- name    : GlobalTheory.CompanionTheory.SW.ModDet.pi_map_diag
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:08:24.856232+00:00
-- url     : https://prove2.me/theorems/b723ad73-a574-42b8-8fcd-fb0afaca435b
-- title:
--   Mod Det: pi map diag
-- statement:
--   The Mod Det construction uses the pi map diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MapMulVecEqSmul.lean#L32-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MapMulVecEqSmul.lean#L32-L41

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

theorem GlobalTheory.CompanionTheory.SW.ModDet.pi_map_diag {ι : Type} [Fintype ι] (lam : Measure K) [lam.IsAddHaarMeasure] (D : ι → Kˣ) :
    (Measure.pi fun _ : ι => lam).map (fun x i => (D i : K) * x i) =
      (∏ i, (distribHaarChar K (D i))⁻¹) • Measure.pi fun _ : ι => lam := by sorry
