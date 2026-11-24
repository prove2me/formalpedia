-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocFv_isOpenEmbedding_units_val
-- name    : GlobalTheory.CompanionTheory.SW.LocFv.isOpenEmbedding_units_val
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:08:46.140514+00:00
-- url     : https://prove2.me/theorems/05007522-8e7e-408b-8419-f3a434293d4c
-- title:
--   Loc Fv: is Open Embedding units val
-- statement:
--   The Loc Fv construction uses the is Open Embedding units val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CompletionIsLocalRing.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CompletionIsLocalRing.lean#L11-L19

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LocFv
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology

theorem GlobalTheory.CompanionTheory.SW.LocFv.isOpenEmbedding_units_val (K : Type) [Field K] [TopologicalSpace K] [ContinuousInv₀ K]
    [ContinuousMul K] [T1Space K] : IsOpenEmbedding (Units.val : Kˣ → K) := by sorry
