-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_rigOfOmega
-- name    : GlobalTheory.PDivGroup.rigExtMap_rigOfOmega
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:02:23.176061+00:00
-- url     : https://prove2.me/theorems/02ae70e6-a875-4d47-a958-cda0909f0bc5
-- title:
--   PDiv Group: rig Ext Map rig Of Omega
-- statement:
--   The PDiv Group construction uses the rig Ext Map rig Of Omega property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EqZeroOfCobOneEqZero.lean#L234-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EqZeroOfCobOneEqZero.lean#L234-L236

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

theorem GlobalTheory.PDivGroup.rigExtMap_rigOfOmega (f : G ⟶ H) (w : H.omega) :
    rigExtMap f (H.rigOfOmega w) = G.rigOfOmega (omegaMap G H f w) := by sorry
