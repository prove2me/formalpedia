-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_partialProd_add
-- name    : GroundTheory.GroupCoh.partialProd_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:12.194605+00:00
-- url     : https://prove2.me/theorems/a8f706b8-7120-4391-a58a-6cc174244d82
-- title:
--   Group Coh: partial Prod add
-- statement:
--   The Group Coh construction uses the partial Prod add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L18-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L18-L29

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

theorem GroundTheory.GroupCoh.partialProd_add {m r p q : ℕ} (x : Fin m → M) (y : Fin r → M) (hpr : p + r ≤ m)
    (hy : ∀ j : Fin r, y j = x ⟨p + j, by omega⟩) (hq : q ≤ r) :
    Fin.partialProd x ⟨p + q, by omega⟩ =
      Fin.partialProd x ⟨p, by omega⟩ * Fin.partialProd y ⟨q, by omega⟩ := by sorry
