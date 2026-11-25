-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_rigToExt_rigExtMap
-- name    : GlobalTheory.PDivGroup.rigToExt_rigExtMap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:59:57.347382+00:00
-- url     : https://prove2.me/theorems/a4d2bd28-ffd6-4202-af2e-888c5e659728
-- title:
--   PDiv Group: rig To Ext rig Ext Map
-- statement:
--   The PDiv Group construction uses the rig To Ext rig Ext Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EqZeroOfCobOneEqZero.lean#L238-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EqZeroOfCobOneEqZero.lean#L238-L241

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

theorem GlobalTheory.PDivGroup.rigToExt_rigExtMap (f : G ⟶ H) (x : H.RigExt) :
    G.rigToExt (rigExtMap f x) = vecExtMap f (H.rigToExt x) := by sorry
