-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HIsom_isTopologicalRing_tens
-- name    : GlobalTheory.CompanionTheory.SW.HIsom.isTopologicalRing_tens
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:24:57.636612+00:00
-- url     : https://prove2.me/theorems/2313ebcd-0a76-413d-bee1-ed6830ee04fc
-- title:
--   HIsom: is Topological Ring tens
-- statement:
--   The HIsom construction uses the is Topological Ring tens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitaryIsomOfIsometry.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitaryIsomOfIsometry.lean#L86-L90

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryIsomOfIsometry
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HIsom

theorem GlobalTheory.CompanionTheory.SW.HIsom.isTopologicalRing_tens (F E : Type) [Field F] [Field E] [Algebra F E] [Module.Finite F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    IsTopologicalRing (R ⊗[F] E) := by sorry
