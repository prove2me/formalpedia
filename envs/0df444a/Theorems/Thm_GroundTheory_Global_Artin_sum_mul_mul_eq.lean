-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_sum_mul_mul_eq
-- name    : GroundTheory.Global.Artin.sum_mul_mul_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:14:31.336661+00:00
-- url     : https://prove2.me/theorems/7273d03b-3af5-47d8-9a44-f8187d898063
-- title:
--   Artin: sum mul mul eq
-- statement:
--   The Artin construction uses the sum mul mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/Mackey.lean#L85-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/Mackey.lean#L85-L154

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_TateCohomology_DoubleCosetSum
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
open GroundTheory.LocalField
variable {G : Type*} [Group G]
variable [Fintype G]
open Classical

theorem GroundTheory.Global.Artin.sum_mul_mul_eq (H D : Subgroup G) [Fintype H] [Fintype D] (x : G) (F : G → ℂ) :
    ∑ h : H, ∑ e : D, F (h * x * e) =
      (Nat.card ((MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D) : ℂ) *
        ∑ u ∈ Finset.univ.filter (fun u ↦ DoubleCoset.mk H D u = DoubleCoset.mk H D x), F u := by sorry
