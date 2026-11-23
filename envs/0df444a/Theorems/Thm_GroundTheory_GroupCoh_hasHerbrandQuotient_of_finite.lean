-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_hasHerbrandQuotient_of_finite
-- name    : GroundTheory.GroupCoh.hasHerbrandQuotient_of_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:58:47.018111+00:00
-- url     : https://prove2.me/theorems/64cd7292-650f-469d-be4c-9fc7e7e145dc
-- title:
--   Group Coh: has Herbrand Quotient of finite
-- statement:
--   The Group Coh construction uses the has Herbrand Quotient of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L67-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L67-L68

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

theorem GroundTheory.GroupCoh.hasHerbrandQuotient_of_finite [Finite A] (f g : A →+ A) : HasHerbrandQuotient f g := by sorry
