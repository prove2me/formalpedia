-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermTop_isModTop
-- name    : GlobalTheory.CompanionTheory.SW.HermTop.isModTop
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:20.810145+00:00
-- url     : https://prove2.me/theorems/dfb2c149-add9-4473-92ce-3f4efea3bfe4
-- title:
--   Herm Top: is Mod Top
-- statement:
--   The Herm Top construction uses the is Mod Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianMatricesLocallyCompactBorel.lean#L40-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianMatricesLocallyCompactBorel.lean#L40-L40

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HermTop
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
variable [TopologicalSpace R] [IsTopologicalRing R]

theorem GlobalTheory.CompanionTheory.SW.HermTop.isModTop : IsModuleTopology R (R ⊗[F] E) := by sorry
