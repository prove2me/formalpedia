-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocFv_isLocR_of_ultrametric
-- name    : GlobalTheory.CompanionTheory.SW.LocFv.isLocR_of_ultrametric
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:09:36.234533+00:00
-- url     : https://prove2.me/theorems/1d632058-f405-418e-8224-23fe37b0a851
-- title:
--   Loc Fv: is Loc R of ultrametric
-- statement:
--   The Loc Fv construction uses the is Loc R of ultrametric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CompletionIsLocalRing.lean#L21-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CompletionIsLocalRing.lean#L21-L84

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

theorem GlobalTheory.CompanionTheory.SW.LocFv.isLocR_of_ultrametric (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
    (h2 : (2 : K) ≠ 0) : IsLocR K := by sorry
