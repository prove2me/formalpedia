-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_Nf_ne
-- name    : GlobalTheory.CompanionTheory.SW.PrimV.Nf_ne
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:06:45.458839+00:00
-- url     : https://prove2.me/theorems/b75c53b9-2bba-43ec-9db6-db0b3e6f9b6d
-- title:
--   Prim V: Nf ne
-- statement:
--   The Prim V construction uses the Nf ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalPrimitiveVectorCompactRescale.lean#L144-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalPrimitiveVectorCompactRescale.lean#L144-L154

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

theorem GlobalTheory.CompanionTheory.SW.PrimV.Nf_ne {D : L} (hD : ∀ s, s * s ≠ D) {p : L × L} (hp : p ≠ 0) : Nf D p ≠ 0 := by sorry
