-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tensorHom_cupCochain
-- name    : GroundTheory.GroupCoh.tensorHom_cupCochain
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:44:17.543505+00:00
-- url     : https://prove2.me/theorems/c69e7b5a-3e8c-4873-807e-a7f16efd8725
-- title:
--   Group Coh: tensor Hom cup Cochain
-- statement:
--   The Group Coh construction uses the tensor Hom cup Cochain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L263-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L263-L269

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

theorem GroundTheory.GroupCoh.tensorHom_cupCochain {A' B' : Rep k G} (φ : A ⟶ A') (ψ : B ⟶ B') (h : p + q = n)
    (f : (Fin p → G) → A) (g : (Fin q → G) → B) (x : Fin n → G) :
    (φ ⊗ₘ ψ).hom (cupCochain h f g x) =
      cupCochain h (fun y => φ.hom (f y)) (fun y => ψ.hom (g y)) x := by sorry
