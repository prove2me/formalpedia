-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_herbrandQuotient_eq_of_injective_of_finite
-- name    : GroundTheory.GroupCoh.herbrandQuotient_eq_of_injective_of_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:41.267448+00:00
-- url     : https://prove2.me/theorems/ac341e91-33f4-44da-b771-854b43d6b0fb
-- title:
--   Group Coh: herbrand Quotient eq of injective of finite
-- statement:
--   The Group Coh construction uses the herbrand Quotient eq of injective of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L479-L495
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L479-L495

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
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem GroundTheory.GroupCoh.herbrandQuotient_eq_of_injective_of_finite {fA gA : A →+ A} {fB gB : B →+ B}
    {i : A →+ B} (hi : Function.Injective i) [Finite (B ⧸ i.range)]
    (hfi : ∀ a, i (fA a) = fB (i a)) (hgi : ∀ a, i (gA a) = gB (i a))
    (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    herbrandQuotient fA gA = herbrandQuotient fB gB := by sorry
