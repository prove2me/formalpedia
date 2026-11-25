-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_whiskerRight_tmul
-- name    : GroundTheory.GroupCoh.whiskerRight_tmul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:12:53.036131+00:00
-- url     : https://prove2.me/theorems/aee43b81-60f9-4c17-a307-47d580b765a9
-- title:
--   Group Coh: whisker Right tmul
-- statement:
--   The Group Coh construction uses the whisker Right tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupConnecting.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupConnecting.lean#L19-L21

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
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
variable {A A' B B' : Rep k G} {p q n : ℕ}

theorem GroundTheory.GroupCoh.whiskerRight_tmul (φ : A ⟶ A') (a : A) (b : B) :
    (φ ▷ B).hom (a ⊗ₜ[k] b : (A ⊗ B : Rep k G)) = φ.hom a ⊗ₜ[k] b := by sorry
