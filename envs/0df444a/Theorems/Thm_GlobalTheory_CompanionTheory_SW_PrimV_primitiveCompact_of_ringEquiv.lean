-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_primitiveCompact_of_ringEquiv
-- name    : GlobalTheory.CompanionTheory.SW.PrimV.primitiveCompact_of_ringEquiv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:08:58.878388+00:00
-- url     : https://prove2.me/theorems/01e8d63a-e231-40ad-ad19-721ebd398290
-- title:
--   Prim V: primitive Compact of ring Equiv
-- statement:
--   The Prim V construction uses the primitive Compact of ring Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalPrimitiveVectorCompactRescale.lean#L76-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalPrimitiveVectorCompactRescale.lean#L76-L89

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

theorem GlobalTheory.CompanionTheory.SW.PrimV.primitiveCompact_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B] {M : ℕ}
    (e : A ≃+* B) (hc : Continuous e.symm) (h : UniP B M) : UniP A M := by sorry
