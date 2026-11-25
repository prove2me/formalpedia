-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_contractNth_prefix_of_le
-- name    : GroundTheory.GroupCoh.contractNth_prefix_of_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:43:35.578033+00:00
-- url     : https://prove2.me/theorems/7e3540cf-38b3-4bf3-a76b-880d7a02c88d
-- title:
--   Group Coh: contract Nth prefix of le
-- statement:
--   The Group Coh construction uses the contract Nth prefix of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L63-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L63-L68

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupCochains
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory MonoidalCategory TensorProduct
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {M : Type*} [Monoid M]
variable {α : Type*}

theorem GroundTheory.GroupCoh.contractNth_prefix_of_le {m p : ℕ} (op : α → α → α) (x : Fin (m + 1) → α)
    (j : Fin (m + 1)) (hj : p ≤ (j : ℕ)) :
    (fun l : Fin p => Fin.contractNth j op x ⟨l, by omega⟩) = fun l : Fin p => x ⟨l, by omega⟩ := by sorry
