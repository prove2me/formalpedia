-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_revCochain_cupCochain
-- name    : GroundTheory.GroupCoh.revCochain_cupCochain
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:15:12.745381+00:00
-- url     : https://prove2.me/theorems/d45471da-2fa9-4ecc-8cb8-72c41325dd61
-- title:
--   Group Coh: rev Cochain cup Cochain
-- statement:
--   The Group Coh construction uses the rev Cochain cup Cochain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupGraded.lean#L20-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupGraded.lean#L20-L61

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
import Definitions.Def_GroundTheory_TateCohomology_CochainReverse
import Definitions.Def_GroundTheory_TateCohomology_CupGraded
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
open CategoryTheory MonoidalCategory TensorProduct groupCohomology
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G] {A B : Rep k G} {p q n : ℕ}

theorem GroundTheory.GroupCoh.revCochain_cupCochain (h : p + q = n) (h' : q + p = n) (f : (Fin p → G) → A)
    (g : (Fin q → G) → B) (x : Fin n → G) :
    revCochain n (cupCochain h f g) x =
      (-1 : k) ^ (p * q) • (β_ B A).hom.hom (cupCochain h' (revCochain q g) (revCochain p f) x) := by sorry
