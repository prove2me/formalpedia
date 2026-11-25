-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_contractNth_suffix_of_lt
-- name    : GroundTheory.GroupCoh.contractNth_suffix_of_lt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:43:35.589912+00:00
-- url     : https://prove2.me/theorems/1096d6ba-f1b8-479a-823c-376fff3729ad
-- title:
--   Group Coh: contract Nth suffix of lt
-- statement:
--   The Group Coh construction uses the contract Nth suffix of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L70-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L70-L78

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

theorem GroundTheory.GroupCoh.contractNth_suffix_of_lt {m p q : ℕ} (op : α → α → α) (x : Fin (m + 1) → α)
    (j : Fin (m + 1)) (hpq : p + q ≤ m) (hj : (j : ℕ) < p) :
    (fun l : Fin q => Fin.contractNth j op x ⟨p + l, by omega⟩) =
      fun l : Fin q => x ⟨p + 1 + l, by omega⟩ := by sorry
