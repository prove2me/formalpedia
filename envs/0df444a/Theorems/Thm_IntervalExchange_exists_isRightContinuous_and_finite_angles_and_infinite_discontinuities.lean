-- Prove2me | Theorems.Thm_IntervalExchange_exists_isRightContinuous_and_finite_angles_and_infinite_discontinuities
-- name    : IntervalExchange.exists_isRightContinuous_and_finite_angles_and_infinite_discontinuities
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T09:24:24.067786+00:00
-- url     : https://prove2.me/theorems/c236430e-ef0c-4de5-825b-f70b647cbfa7
-- title:
--   A right-continuous permutation of ℝ/ℤ with finitely many angles can have infinitely many discontinuities
-- statement:
--   There is a permutation $g$ of the circle $\mathbf R/\mathbf Z$ that is right-continuous at every point and has only finitely many angles $g(x) - x$, but has infinitely many points of discontinuity.
--
--   Juschenko, Matte Bon, Monod and de la Salle, p. 4: “An interval exchange transformation is a permutation of a circle obtained by cutting this circle into finitely many intervals (arcs), and reordering them. More precisely, an interval exchange transformation is a right-continuous permutation $g$ of $\mathbf R/\mathbf Z$ such that the set $\{gx - x, x \in \mathbf R/\mathbf Z\}$, called the set of angles of $g$, is finite.”
--
--   The second sentence alone therefore admits maps that are not obtained by cutting the circle into finitely many arcs. The definition of an interval exchange transformation in the IET mission's definitions item (`IntervalExchange.IsIntervalExchange`) also requires finitely many points of discontinuity, following the first sentence.
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 4, the definition of an interval exchange transformation (printed-fails lemma, not in the paper)

import Mathlib
import Definitions.Def_IntervalExchange

namespace IntervalExchange

theorem exists_isRightContinuous_and_finite_angles_and_infinite_discontinuities :
    ∃ g : Equiv.Perm UnitAddCircle,
      IsRightContinuous g ∧ (angles g).Finite ∧ ¬ {x | ¬ ContinuousAt g x}.Finite := by
  sorry

end IntervalExchange
