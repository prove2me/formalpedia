-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_repr_mul
-- name    : GlobalTheory.CompanionTheory.SW.PrimGood.repr_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:30:37.461371+00:00
-- url     : https://prove2.me/theorems/f5b5a517-bd44-4b67-87e7-adf306b580d5
-- title:
--   Prim Good: repr mul
-- statement:
--   The Prim Good construction uses the repr mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PrimitiveVectorLatticeRescaleAlmostAll.lean#L77-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PrimitiveVectorLatticeRescaleAlmostAll.lean#L77-L93

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PrimitiveVectorLatticeRescaleAlmostAll
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimGood
variable {L K : Type} [Field L] [CommRing K] [Algebra L K] (B : Module.Basis (Fin 2) L K)
variable {B} {Δ : L}

theorem GlobalTheory.CompanionTheory.SW.PrimGood.repr_mul (h0 : B 0 = 1) (h1 : B 1 * B 1 = algebraMap L K Δ) (x y : K) :
    B.repr (x * y) 0 = B.repr x 0 * B.repr y 0 + Δ * (B.repr x 1 * B.repr y 1) ∧
    B.repr (x * y) 1 = B.repr x 0 * B.repr y 1 + B.repr x 1 * B.repr y 0 := by sorry
