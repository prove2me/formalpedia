-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_leftUnitor_hom_tmul
-- name    : GroundTheory.GroupCoh.leftUnitor_hom_tmul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:43:38.97488+00:00
-- url     : https://prove2.me/theorems/130ad98e-df41-4555-98c7-aa393cb54371
-- title:
--   Group Coh: left Unitor hom tmul
-- statement:
--   The Group Coh construction uses the left Unitor hom tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L231-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L231-L233

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

theorem GroundTheory.GroupCoh.leftUnitor_hom_tmul (X : Rep k G) (c : k) (a : X) :
    (λ_ X).hom.hom ((c ⊗ₜ[k] a : (𝟙_ (Rep k G) ⊗ X : Rep k G))) = c • a := by sorry
