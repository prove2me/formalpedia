-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_rr_add
-- name    : GlobalTheory.CompanionTheory.SW.PrimV.rr_add
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:10:50.326126+00:00
-- url     : https://prove2.me/theorems/f6f23e1b-5a54-4702-82b9-f39c9621be8a
-- title:
--   Prim V: rr add
-- statement:
--   The Prim V construction uses the rr add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalPrimitiveVectorCompactRescale.lean#L124-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalPrimitiveVectorCompactRescale.lean#L124-L124

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

theorem GlobalTheory.CompanionTheory.SW.PrimV.rr_add (x y : K) : rr bs (x + y) = rr bs x + rr bs y := by sorry
