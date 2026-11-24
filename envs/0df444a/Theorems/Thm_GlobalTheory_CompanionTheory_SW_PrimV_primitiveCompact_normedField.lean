-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_primitiveCompact_normedField
-- name    : GlobalTheory.CompanionTheory.SW.PrimV.primitiveCompact_normedField
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:11:26.936598+00:00
-- url     : https://prove2.me/theorems/48090bb6-76d4-493d-8d2a-6badc990ef5f
-- title:
--   Prim V: primitive Compact normed Field
-- statement:
--   The Prim V construction uses the primitive Compact normed Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalPrimitiveVectorCompactRescale.lean#L246-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalPrimitiveVectorCompactRescale.lean#L246-L252

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
variable {L K : Type*} [NormedField L] [ProperSpace L]
variable [CommRing K] [Algebra L K] [TopologicalSpace K] (bs : Module.Basis (Fin 2) L K)

theorem GlobalTheory.CompanionTheory.SW.PrimV.primitiveCompact_normedField (M : ℕ) : UniP L M := by sorry
