-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_whiskerRight_cupCochain
-- name    : GroundTheory.GroupCoh.whiskerRight_cupCochain
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:12:57.360603+00:00
-- url     : https://prove2.me/theorems/f2fdef18-45ee-49ce-a7a1-0445f02f097e
-- title:
--   Group Coh: whisker Right cup Cochain
-- statement:
--   The Group Coh construction uses the whisker Right cup Cochain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupConnecting.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupConnecting.lean#L27-L30

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

theorem GroundTheory.GroupCoh.whiskerRight_cupCochain (φ : A ⟶ A') (h : p + q = n) (f : (Fin p → G) → A)
    (g : (Fin q → G) → B) (x : Fin n → G) :
    (φ ▷ B).hom (cupCochain h f g x) = cupCochain h (fun v => φ.hom (f v)) g x := by sorry
