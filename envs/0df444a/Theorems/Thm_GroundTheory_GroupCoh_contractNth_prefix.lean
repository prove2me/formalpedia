-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_contractNth_prefix
-- name    : GroundTheory.GroupCoh.contractNth_prefix
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:43:28.48358+00:00
-- url     : https://prove2.me/theorems/24c9b60c-bd12-4af8-b505-3012cafff638
-- title:
--   Group Coh: contract Nth prefix
-- statement:
--   The Group Coh construction uses the contract Nth prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L55-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L55-L61

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

theorem GroundTheory.GroupCoh.contractNth_prefix {m p : ℕ} (op : α → α → α) (x : Fin (m + 1) → α) (j : Fin (m + 1))
    (j' : Fin (p + 1)) (hp : p ≤ m) (hj : (j : ℕ) = j') :
    (fun l : Fin p => Fin.contractNth j op x ⟨l, by omega⟩) =
      Fin.contractNth j' op (fun l : Fin (p + 1) => x ⟨l, by omega⟩) := by sorry
