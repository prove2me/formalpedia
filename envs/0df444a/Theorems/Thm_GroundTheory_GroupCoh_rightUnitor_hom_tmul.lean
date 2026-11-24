-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_rightUnitor_hom_tmul
-- name    : GroundTheory.GroupCoh.rightUnitor_hom_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:13.461098+00:00
-- url     : https://prove2.me/theorems/395da05b-2721-4c29-9e1b-4d4358f12c91
-- title:
--   Group Coh: right Unitor hom tmul
-- statement:
--   The Group Coh construction uses the right Unitor hom tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L235-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L235-L237

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

theorem GroundTheory.GroupCoh.rightUnitor_hom_tmul (X : Rep k G) (a : X) (c : k) :
    (ρ_ X).hom.hom ((a ⊗ₜ[k] c : (X ⊗ 𝟙_ (Rep k G) : Rep k G))) = c • a := by sorry
