-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_exists_inv
-- name    : GlobalTheory.CompanionTheory.SW.PrimGood.exists_inv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:08:22.825238+00:00
-- url     : https://prove2.me/theorems/278571c9-b7f4-4e2b-b395-eada9340ba8b
-- title:
--   Prim Good: exists inv
-- statement:
--   The Prim Good construction uses the exists inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PrimitiveVectorLatticeRescaleAlmostAll.lean#L110-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PrimitiveVectorLatticeRescaleAlmostAll.lean#L110-L122

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

theorem GlobalTheory.CompanionTheory.SW.PrimGood.exists_inv (h0 : B 0 = 1) (h1 : B 1 * B 1 = algebraMap L K Δ) (x : K)
    (hN : nrm B Δ x ≠ 0) : ∃ x', x * x' = 1 := by sorry
