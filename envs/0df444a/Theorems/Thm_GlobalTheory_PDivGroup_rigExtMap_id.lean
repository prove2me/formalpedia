-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_id
-- name    : GlobalTheory.PDivGroup.rigExtMap_id
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:59:04.970627+00:00
-- url     : https://prove2.me/theorems/5ece2dd5-b465-47d0-9e59-ef2651d04f07
-- title:
--   PDiv Group: rig Ext Map id
-- statement:
--   The PDiv Group construction uses the rig Ext Map id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EqZeroOfCobOneEqZero.lean#L221-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EqZeroOfCobOneEqZero.lean#L221-L225

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
variable {G H K}
variable [Fact p.Prime]

theorem GlobalTheory.PDivGroup.rigExtMap_id : rigExtMap (𝟙 G) = LinearMap.id := by sorry
