-- Prove2me | Theorems.Thm_GlobalTheory_ClassIntegral_measurableSet_dcoset
-- name    : GlobalTheory.ClassIntegral.measurableSet_dcoset
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:27:06.879685+00:00
-- url     : https://prove2.me/theorems/4698c9dd-9956-4092-91bf-3dc60cf06267
-- title:
--   Class Integral: measurable Set dcoset
-- statement:
--   The Class Integral construction uses the measurable Set dcoset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralFundamentalDomainEqSum.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralFundamentalDomainEqSum.lean#L11-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralFundamentalDomainEqSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.ClassIntegral
variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem GlobalTheory.ClassIntegral.measurableSet_dcoset (Γ K : Subgroup G) [Countable Γ] (hK : MeasurableSet (K : Set G)) (g : G) :
    MeasurableSet (dcoset Γ K g) := by sorry
