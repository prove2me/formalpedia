-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_primitiveCompact_of_multiplicative
-- name    : GlobalTheory.CompanionTheory.SW.PrimV.primitiveCompact_of_multiplicative
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:07:29.084936+00:00
-- url     : https://prove2.me/theorems/a53edc41-8389-4ce0-8866-3ffb2f40ebba
-- title:
--   Prim V: primitive Compact of multiplicative
-- statement:
--   The Prim V construction uses the primitive Compact of multiplicative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalPrimitiveVectorCompactRescale.lean#L17-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalPrimitiveVectorCompactRescale.lean#L17-L49

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

theorem GlobalTheory.CompanionTheory.SW.PrimV.primitiveCompact_of_multiplicative {K : Type*} [CommRing K] [Nontrivial K] [TopologicalSpace K] (M : ℕ) (ν : K → ℝ)
    (h0 : ν 0 = 0) (h1 : ν 1 = 1) (hm : ∀ x y, ν (x * y) = ν x * ν y) (hn : ∀ x, 0 ≤ ν x)
    (hu : ∀ x, x ≠ 0 → IsUnit x ∧ 0 < ν x) (hc : IsCompact {x | ν x ≤ 1}) : UniP K M := by sorry
