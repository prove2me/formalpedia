-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_natCard_kerModRange_eq_of_finite
-- name    : GroundTheory.GroupCoh.natCard_kerModRange_eq_of_finite
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:08.0958+00:00
-- url     : https://prove2.me/theorems/43dd6c5a-280e-4be3-bbb1-7dff7e43976b
-- title:
--   Group Coh: nat Card ker Mod Range eq of finite
-- statement:
--   The Group Coh construction uses the nat Card ker Mod Range eq of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L70-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L70-L83

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.GroupCoh
variable {A : Type*} [AddCommGroup A]

theorem GroundTheory.GroupCoh.natCard_kerModRange_eq_of_finite [Finite A] {f g : A →+ A} (hfg : ∀ x, f (g x) = 0)
    (hgf : ∀ x, g (f x) = 0) : Nat.card (KerModRange f g) = Nat.card (KerModRange g f) := by sorry
