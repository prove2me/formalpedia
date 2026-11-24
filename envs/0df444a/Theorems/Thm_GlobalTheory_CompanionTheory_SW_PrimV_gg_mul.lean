-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_gg_mul
-- name    : GlobalTheory.CompanionTheory.SW.PrimV.gg_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:08:11.356878+00:00
-- url     : https://prove2.me/theorems/64a55441-ef6c-4fbd-b313-b75f86536349
-- title:
--   Prim V: gg mul
-- statement:
--   The Prim V construction uses the gg mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalPrimitiveVectorCompactRescale.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalPrimitiveVectorCompactRescale.lean#L97-L100

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

theorem GlobalTheory.CompanionTheory.SW.PrimV.gg_mul {d : K} {D : L} (hd : d * d = algebraMap L K D) (p q : L × L) :
    gg d p * gg d q = gg d (p.1 * q.1 + D * (p.2 * q.2), p.1 * q.2 + p.2 * q.1) := by sorry
