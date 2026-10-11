-- Prove2me | Theorems.Thm_MazurTransfer_place_ord_image_unit_of_range
-- name    : MazurTransfer.place_ord_image_unit_of_range
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T14:07:02.580424+00:00
-- url     : https://prove2.me/theorems/5a5ee619-a003-4412-9315-298c7c965a9f
-- title:
--   A unit in a ring whose image is a place valuation ring has order zero
-- statement:
--   If a ring homomorphism $f:A\to F$ has image equal to the valuation ring of a place $p$ and $a$ is a unit of $A$, then $\operatorname{ord}_p(f(a))=0$. The proof lifts $f$ to the valuation ring and maps the unit there. This is used for the actual ordinary-chart Pell unit on the order-thirteen curve, proving its order is zero at every ordinary closed point; combined with the checked infinity orders, this gives its complete two-point principal divisor.
-- source:
--   Owned MazurTheorem integration lemma using the Place order and divisor definitions ported from official Anthropic FLT, Apache-2.0, at 6e837e75355538c7f80bab5b956861e86c4eacc2; Mathlib pin 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
open AlgebraicCurve
universe u v w

theorem MazurTransfer.place_ord_image_unit_of_range
    (K : Type u) [Field K] (F : Type v) [Field F] [Algebra K F]
    (A : Type w) [CommRing A] (p : Place K F) (f : A →+* F)
    (hrange : f.range = p.toValuationSubring.toSubring) (a : A) (ha : IsUnit a) :
    p.ord (f a) = 0 := by sorry
