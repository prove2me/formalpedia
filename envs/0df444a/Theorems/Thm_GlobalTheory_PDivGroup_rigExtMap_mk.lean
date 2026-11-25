-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_mk
-- name    : GlobalTheory.PDivGroup.rigExtMap_mk
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:59:29.832254+00:00
-- url     : https://prove2.me/theorems/0a7048e7-1f18-43e4-95c5-63e251762f49
-- title:
--   PDiv Group: rig Ext Map mk
-- statement:
--   The PDiv Group construction uses the rig Ext Map mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EqZeroOfCobOneEqZero.lean#L218-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EqZeroOfCobOneEqZero.lean#L218-L219

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

theorem GlobalTheory.PDivGroup.rigExtMap_mk (f : G ⟶ H) (c : H.cocycles) (w : H.omega) :
    rigExtMap f (H.rigMk (c, w)) = G.rigMk (cocyclesMap f c, omegaMap G H f w) := by sorry

attribute [defeq] GlobalTheory.PDivGroup.rigExtMap_mk
