-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_d_cupCochain
-- name    : GroundTheory.GroupCoh.d_cupCochain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:12.621707+00:00
-- url     : https://prove2.me/theorems/fc1d9cfe-090f-4308-aeb1-19ec30183b46
-- title:
--   Group Coh: d cup Cochain
-- statement:
--   The Group Coh construction uses the d cup Cochain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L113-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L113-L204

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

theorem GroundTheory.GroupCoh.d_cupCochain (h : p + q = n) (f : (Fin p → G) → A) (g : (Fin q → G) → B) :
    (inhomogeneousCochains.d (A ⊗ B) n).hom (cupCochain h f g) =
      cupCochain (by omega) ((inhomogeneousCochains.d A p).hom f) g +
        (-1 : k) ^ p • cupCochain (by omega) f ((inhomogeneousCochains.d B q).hom g) := by sorry
