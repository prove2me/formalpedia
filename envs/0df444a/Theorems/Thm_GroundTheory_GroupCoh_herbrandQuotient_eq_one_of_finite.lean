-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_herbrandQuotient_eq_one_of_finite
-- name    : GroundTheory.GroupCoh.herbrandQuotient_eq_one_of_finite
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:43:24.044034+00:00
-- url     : https://prove2.me/theorems/44095506-2818-4fcd-a4eb-95dbd3f70b12
-- title:
--   Group Coh: herbrand Quotient eq one of finite
-- statement:
--   The Group Coh construction uses the herbrand Quotient eq one of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L85-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L85-L89

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

theorem GroundTheory.GroupCoh.herbrandQuotient_eq_one_of_finite [Finite A] {f g : A →+ A} (hfg : ∀ x, f (g x) = 0)
    (hgf : ∀ x, g (f x) = 0) : herbrandQuotient f g = 1 := by sorry
