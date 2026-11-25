-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_whiskerLeft_tmul
-- name    : GroundTheory.GroupCoh.whiskerLeft_tmul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:13:48.29258+00:00
-- url     : https://prove2.me/theorems/6eb42eec-c19e-46cd-ab83-472cf535a749
-- title:
--   Group Coh: whisker Left tmul
-- statement:
--   The Group Coh construction uses the whisker Left tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupConnecting.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupConnecting.lean#L23-L25

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

theorem GroundTheory.GroupCoh.whiskerLeft_tmul (ψ : B ⟶ B') (a : A) (b : B) :
    (A ◁ ψ).hom (a ⊗ₜ[k] b : (A ⊗ B : Rep k G)) = a ⊗ₜ[k] ψ.hom b := by sorry
