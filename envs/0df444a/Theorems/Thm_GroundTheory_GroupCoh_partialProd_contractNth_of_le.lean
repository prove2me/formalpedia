-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_partialProd_contractNth_of_le
-- name    : GroundTheory.GroupCoh.partialProd_contractNth_of_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:43:21.433907+00:00
-- url     : https://prove2.me/theorems/2b837488-ae1d-409a-8982-5a5b03a1cc47
-- title:
--   Group Coh: partial Prod contract Nth of le
-- statement:
--   The Group Coh construction uses the partial Prod contract Nth of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L42-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L42-L51

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

theorem GroundTheory.GroupCoh.partialProd_contractNth_of_le {m p : ℕ} (x : Fin (m + 1) → M) (j : Fin (m + 1))
    (hp : p ≤ m) (hj : p ≤ (j : ℕ)) :
    Fin.partialProd (Fin.contractNth j (· * ·) x) ⟨p, by omega⟩ =
      Fin.partialProd x ⟨p, by omega⟩ := by sorry
