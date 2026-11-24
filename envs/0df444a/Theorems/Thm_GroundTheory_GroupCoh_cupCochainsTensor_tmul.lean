-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_cupCochainsTensor_tmul
-- name    : GroundTheory.GroupCoh.cupCochainsTensor_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:06.51151+00:00
-- url     : https://prove2.me/theorems/cd831536-ecb1-4ded-8d18-bd77d2118d34
-- title:
--   Group Coh: cup Cochains Tensor tmul
-- statement:
--   The Group Coh construction uses the cup Cochains Tensor tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L259-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L259-L261

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

theorem GroundTheory.GroupCoh.cupCochainsTensor_tmul (f : (Fin p → G) → A) (g : (Fin q → G) → B) :
    cupCochainsTensor A B p q (f ⊗ₜ g) = cupCochain rfl f g := by sorry

attribute [defeq] GroundTheory.GroupCoh.cupCochainsTensor_tmul
