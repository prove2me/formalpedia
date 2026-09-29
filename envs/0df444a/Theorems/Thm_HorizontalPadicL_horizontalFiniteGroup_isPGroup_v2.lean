-- Prove2me | Theorems.Thm_HorizontalPadicL_horizontalFiniteGroup_isPGroup_v2
-- name    : HorizontalPadicL.horizontalFiniteGroup_isPGroup_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T11:41:03.218386+00:00
-- url     : https://prove2.me/theorems/a0429464-ba69-45f9-8951-5b7ee90bba15
-- title:
--   Finite horizontal quotients are p-groups
-- statement:
--   Every finite horizontal quotient, being a finite product of additive groups Z/p^{m_i}Z, is a finite p-group.
-- source:
--   Elementary finite abelian group theory.

import Definitions.Def_KN_SeededThetaConstructionV2B
import Mathlib.GroupTheory.PGroup

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- Every finite horizontal quotient is a finite `p`-group. -/
theorem horizontalFiniteGroup_isPGroup_v2
    {p : ℕ} [Fact p.Prime] (m : ℕ → ℕ) (A : Finset ℕ) :
    IsPGroup p (HorizontalFiniteGroup p m A) := by sorry

end HorizontalPadicL
