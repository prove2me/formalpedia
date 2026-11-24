-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_int_ef
-- name    : GlobalTheory.CompanionTheory.SW.PrimGood.int_ef
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:08:03.019349+00:00
-- url     : https://prove2.me/theorems/707ca867-2953-461e-80c8-f46b046f1086
-- title:
--   Prim Good: int ef
-- statement:
--   The Prim Good construction uses the int ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PrimitiveVectorLatticeRescaleAlmostAll.lean#L191-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PrimitiveVectorLatticeRescaleAlmostAll.lean#L191-L196

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

theorem GlobalTheory.CompanionTheory.SW.PrimGood.int_ef {e f : K} (he : ∀ l, w (B.repr e l) ≤ 1) (hf : ∀ l, w (B.repr f l) ≤ 1) {α β : L}
    (hα : w α ≤ 1) (hβ : w β ≤ 1) (l : Fin 2) : w (B.repr (α • e + β • f) l) ≤ 1 := by sorry
