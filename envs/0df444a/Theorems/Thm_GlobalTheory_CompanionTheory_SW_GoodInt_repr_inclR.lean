-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodInt_repr_inclR
-- name    : GlobalTheory.CompanionTheory.SW.GoodInt.repr_inclR
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:24:38.747489+00:00
-- url     : https://prove2.me/theorems/a745dd0f-3552-49f4-971f-111ab0e0a7de
-- title:
--   Good Int: repr incl R
-- statement:
--   The Good Int construction uses the repr incl R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IntegralAlmostAllPlaces.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IntegralAlmostAllPlaces.lean#L26-L31

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GoodInt

theorem GlobalTheory.CompanionTheory.SW.GoodInt.repr_inclR {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (R : Type) [CommRing R] [Algebra F R] (x : E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (inclR R x) k = algebraMap F R (b.repr x k) := by sorry
