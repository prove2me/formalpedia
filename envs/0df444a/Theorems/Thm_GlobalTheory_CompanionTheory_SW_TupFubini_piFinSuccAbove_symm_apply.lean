-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TupFubini_piFinSuccAbove_symm_apply
-- name    : GlobalTheory.CompanionTheory.SW.TupFubini.piFinSuccAbove_symm_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:15.269876+00:00
-- url     : https://prove2.me/theorems/f6e67862-a2a2-4d03-9c66-cc7fcab981cd
-- title:
--   Tup Fubini: pi Fin Succ Above symm apply
-- statement:
--   The Tup Fubini construction uses the pi Fin Succ Above symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberMeasureOrthogonalExtension.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberMeasureOrthogonalExtension.lean#L22-L26

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryActionPreservesHaarLocalStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureOrthogonalExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TupFubini
variable {T : Type} [MeasurableSpace T]

theorem GlobalTheory.CompanionTheory.SW.TupFubini.piFinSuccAbove_symm_apply {A : Type} [MeasurableSpace A] {n : ℕ} (x : A) (Y : Fin n → A) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => A) 0).symm (x, Y) = Fin.cons x Y := by sorry
