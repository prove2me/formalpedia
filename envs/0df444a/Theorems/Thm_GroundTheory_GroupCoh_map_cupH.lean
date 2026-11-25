-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_map_cupH
-- name    : GroundTheory.GroupCoh.map_cupH
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:58:37.655012+00:00
-- url     : https://prove2.me/theorems/b8e44144-5d47-4fcc-864d-7efcd5a7e431
-- title:
--   Group Coh: map cup H
-- statement:
--   The Group Coh construction uses the map cup H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupProduct.lean#L180-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupProduct.lean#L180-L194

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupCochains
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
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
open CategoryTheory MonoidalCategory TensorProduct groupCohomology Limits
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {A B : Rep k G} {p q n : ℕ}

theorem GroundTheory.GroupCoh.map_cupH {A' B' : Rep k G} (φ : A ⟶ A') (ψ : B ⟶ B') (h : p + q = n)
    (a : groupCohomology A p) (b : groupCohomology B q) :
    map (MonoidHom.id G) (φ ⊗ₘ ψ) n (cupH h a b) =
      cupH h (map (MonoidHom.id G) φ p a) (map (MonoidHom.id G) ψ q b) := by sorry
