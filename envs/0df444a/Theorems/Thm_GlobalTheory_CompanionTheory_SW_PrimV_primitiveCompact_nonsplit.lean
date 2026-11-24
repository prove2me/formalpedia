-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_primitiveCompact_nonsplit
-- name    : GlobalTheory.CompanionTheory.SW.PrimV.primitiveCompact_nonsplit
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:09:25.002322+00:00
-- url     : https://prove2.me/theorems/063b609f-b240-49bb-9ee9-6f6054e6009c
-- title:
--   Prim V: primitive Compact nonsplit
-- statement:
--   The Prim V construction uses the primitive Compact nonsplit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalPrimitiveVectorCompactRescale.lean#L205-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalPrimitiveVectorCompactRescale.lean#L205-L244

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

theorem GlobalTheory.CompanionTheory.SW.PrimV.primitiveCompact_nonsplit (h0 : bs 0 = 1) {D : L} (hd : bs 1 * bs 1 = algebraMap L K D)
    (hD : ∀ s, s * s ≠ D) (hg : Continuous (gg (bs 1) : L × L → K)) (M : ℕ) : UniP K M := by sorry
