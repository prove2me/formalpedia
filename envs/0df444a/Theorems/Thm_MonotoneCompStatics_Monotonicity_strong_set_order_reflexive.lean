-- Prove2me | Theorems.Thm_MonotoneCompStatics_Monotonicity_strong_set_order_reflexive
-- name    : MonotoneCompStatics.Monotonicity.strong_set_order_reflexive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:39.976722+00:00
-- url     : https://prove2.me/theorems/9986658b-799c-4bd6-8afc-19d0d2e3fd01
-- title:
--   p. 159 remark: reflexivity of the strong set order
-- statement:
--   Let $X$ be a lattice and $S\subseteq X$. The strong set order is reflexive at $S$ exactly when $S$ is closed under meet and join:
--
--   $$S\le_s S\quad\Longleftrightarrow\quad S\text{ is a sublattice of }X.$$
--
--   This identifies the feasible sets for which comparing an optimization problem to itself by the strong set order is meaningful. The equivalence also holds for the empty set, since both conditions are vacuous there.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), p. 159 (PDF 4), remark on reflexivity of the strong set order

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder

namespace MonotoneCompStatics.Monotonicity

theorem strong_set_order_reflexive {X : Type*} [Lattice X] (S : Set X) :
    Supermodularity.Lattices.InducedSetOrder S S ↔ IsSublattice S := by sorry

end MonotoneCompStatics.Monotonicity
