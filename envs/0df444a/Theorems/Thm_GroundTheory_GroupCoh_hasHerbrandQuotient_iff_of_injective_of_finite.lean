-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_hasHerbrandQuotient_iff_of_injective_of_finite
-- name    : GroundTheory.GroupCoh.hasHerbrandQuotient_iff_of_injective_of_finite
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:58:49.052693+00:00
-- url     : https://prove2.me/theorems/ae001f0c-e8d4-4117-a8e1-c809eb8b0de7
-- title:
--   Group Coh: has Herbrand Quotient iff of injective of finite
-- statement:
--   The Group Coh construction uses the has Herbrand Quotient iff of injective of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L461-L477
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L461-L477

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

theorem GroundTheory.GroupCoh.hasHerbrandQuotient_iff_of_injective_of_finite {fA gA : A →+ A} {fB gB : B →+ B}
    {i : A →+ B} (hi : Function.Injective i) [Finite (B ⧸ i.range)]
    (hfi : ∀ a, i (fA a) = fB (i a)) (hgi : ∀ a, i (gA a) = gB (i a))
    (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    HasHerbrandQuotient fA gA ↔ HasHerbrandQuotient fB gB := by sorry
