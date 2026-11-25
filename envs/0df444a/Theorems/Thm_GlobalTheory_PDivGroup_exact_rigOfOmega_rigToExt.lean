-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_exact_rigOfOmega_rigToExt
-- name    : GlobalTheory.PDivGroup.exact_rigOfOmega_rigToExt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:59:43.405868+00:00
-- url     : https://prove2.me/theorems/b2383e6d-3614-418a-8460-141cd45fcd43
-- title:
--   PDiv Group: exact rig Of Omega rig To Ext
-- statement:
--   The PDiv Group construction uses the exact rig Of Omega rig To Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EqZeroOfCobOneEqZero.lean#L160-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EqZeroOfCobOneEqZero.lean#L160-L169

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EqZeroOfCobOneEqZero_fe26957659067348
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv
variable {p : ℕ} {O : Type} [CommRing O] (G H K : PDivGroup p O)

theorem GlobalTheory.PDivGroup.exact_rigOfOmega_rigToExt : Function.Exact G.rigOfOmega G.rigToExt := by sorry
