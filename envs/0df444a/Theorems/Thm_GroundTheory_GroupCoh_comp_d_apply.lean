-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_comp_d_apply
-- name    : GroundTheory.GroupCoh.comp_d_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:12:48.553916+00:00
-- url     : https://prove2.me/theorems/6e23104f-5f4a-4e02-bc3e-7dc5c5aff020
-- title:
--   Group Coh: comp d apply
-- statement:
--   The Group Coh construction uses the comp d apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupConnecting.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupConnecting.lean#L43-L47

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
variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact)

theorem GroundTheory.GroupCoh.comp_d_apply {A A' : Rep k G} (φ : A ⟶ A') (i : ℕ) (y : (Fin i → G) → A)
    (v : Fin (i + 1) → G) :
    φ.hom ((inhomogeneousCochains.d A i).hom y v) =
      (inhomogeneousCochains.d A' i).hom (fun u => φ.hom (y u)) v := by sorry
