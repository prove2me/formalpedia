-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_mul_ef
-- name    : GlobalTheory.CompanionTheory.SW.PrimGood.mul_ef
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:08:22.349432+00:00
-- url     : https://prove2.me/theorems/186e86b5-6fee-417a-a1f6-305987039c49
-- title:
--   Prim Good: mul ef
-- statement:
--   The Prim Good construction uses the mul ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PrimitiveVectorLatticeRescaleAlmostAll.lean#L184-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PrimitiveVectorLatticeRescaleAlmostAll.lean#L184-L189

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
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)

theorem GlobalTheory.CompanionTheory.SW.PrimGood.mul_ef {e f : K} (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) (α β γ δ : L) :
    (α • e + β • f) * (γ • e + δ • f) = (α * γ) • e + (β * δ) • f := by sorry
