-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_partialProd_prefix
-- name    : GroundTheory.GroupCoh.partialProd_prefix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:12.888806+00:00
-- url     : https://prove2.me/theorems/01c702dd-4390-4f07-86c8-79e7f2d91f67
-- title:
--   Group Coh: partial Prod prefix
-- statement:
--   The Group Coh construction uses the partial Prod prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L206-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L206-L216

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
variable {A B : Rep k G} {p q n : ℕ}

theorem GroundTheory.GroupCoh.partialProd_prefix {M : Type*} [Monoid M] {m m' j : ℕ} (x : Fin m' → M) (hm : m ≤ m')
    (hj : j ≤ m) :
    Fin.partialProd (fun i : Fin m => x ⟨i, by omega⟩) ⟨j, by omega⟩ =
      Fin.partialProd x ⟨j, by omega⟩ := by sorry
