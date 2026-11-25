-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_rigToExt_surjective
-- name    : GlobalTheory.PDivGroup.rigToExt_surjective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:01:52.534553+00:00
-- url     : https://prove2.me/theorems/c9132732-3a01-48e4-ad76-4a19b840a3e0
-- title:
--   PDiv Group: rig To Ext surjective
-- statement:
--   The PDiv Group construction uses the rig To Ext surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EqZeroOfCobOneEqZero.lean#L156-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EqZeroOfCobOneEqZero.lean#L156-L158

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

theorem GlobalTheory.PDivGroup.rigToExt_surjective : Function.Surjective G.rigToExt := by sorry
