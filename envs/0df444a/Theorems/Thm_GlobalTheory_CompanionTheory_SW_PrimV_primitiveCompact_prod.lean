-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_primitiveCompact_prod
-- name    : GlobalTheory.CompanionTheory.SW.PrimV.primitiveCompact_prod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:10:25.979106+00:00
-- url     : https://prove2.me/theorems/3cef33eb-6737-4bde-af13-76d88f763cea
-- title:
--   Prim V: primitive Compact prod
-- statement:
--   The Prim V construction uses the primitive Compact prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalPrimitiveVectorCompactRescale.lean#L51-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalPrimitiveVectorCompactRescale.lean#L51-L74

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

theorem GlobalTheory.CompanionTheory.SW.PrimV.primitiveCompact_prod {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B] {M : ℕ}
    (hA : UniP A M) (hB : UniP B M) : UniP (A × B) M := by sorry
