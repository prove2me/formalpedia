-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocFv_isLocR_Fv
-- name    : GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:05:30.553439+00:00
-- url     : https://prove2.me/theorems/f63a1520-7e8e-47a8-a9c9-1757fc955d10
-- title:
--   Loc Fv: is Loc R Fv
-- statement:
--   The Loc Fv construction uses the is Loc R Fv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CompletionIsLocalRing.lean#L86-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CompletionIsLocalRing.lean#L86-L95

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

theorem GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), IsLocR (Fv F v) := by sorry
