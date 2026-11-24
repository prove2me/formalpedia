-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_rr_mul
-- name    : GlobalTheory.CompanionTheory.SW.PrimV.rr_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:06:00.025338+00:00
-- url     : https://prove2.me/theorems/579a8ee3-14fe-4fd8-b98b-0dbf887e0ad6
-- title:
--   Prim V: rr mul
-- statement:
--   The Prim V construction uses the rr mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalPrimitiveVectorCompactRescale.lean#L114-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalPrimitiveVectorCompactRescale.lean#L114-L117

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalPrimitiveVectorCompactRescale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimV
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {L K : Type*} [Field L] [CommRing K] [Algebra L K]
variable (bs : Module.Basis (Fin 2) L K)

theorem GlobalTheory.CompanionTheory.SW.PrimV.rr_mul (h0 : bs 0 = 1) {D : L} (hd : bs 1 * bs 1 = algebraMap L K D) (x y : K) :
    rr bs (x * y) = ((rr bs x).1 * (rr bs y).1 + D * ((rr bs x).2 * (rr bs y).2),
      (rr bs x).1 * (rr bs y).2 + (rr bs x).2 * (rr bs y).1) := by sorry
