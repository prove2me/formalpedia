-- Prove2me | Theorems.Thm_HomeoLine_pairwise_disjoint_zpow_image
-- name    : HomeoLine.pairwise_disjoint_zpow_image
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-13T08:43:46.556831+00:00
-- url     : https://prove2.me/theorems/e1491373-5927-40aa-ad9c-fa59f23a01f7
-- title:
--   Iterated images of an interval under a map that pushes it forward are pairwise disjoint
-- statement:
--   Let $z$ be an order isomorphism of $\mathbb{R}$ and let $c \le d$ satisfy $z(c) > d$ — so $z$ carries the interval $[c,d]$ entirely beyond itself. Then the iterated images
--
--   $$\bigl(z^{m}(c),\ z^{m}(d)\bigr), \qquad m \in \mathbb{Z},$$
--
--   are pairwise disjoint.
--
--   Monotonicity does all the work: applying the increasing map $z^{k}$ to $d < z(c)$ gives $z^{k}(d) < z^{k+1}(c)$, so each interval ends strictly before the next one begins, and the family is strictly increasing along $\mathbb{Z}$. Negative exponents are included, the chain extending in both directions.
--
--   **Role.** The step that turns a *single* element with confined moved set into an **infinite** family of elements with pairwise disjoint moved sets: conjugating by $z^{m}$ transports the moved set into the $m$-th interval. Combined with the general form of Lemma (1.2), that is what produces a free abelian group of infinite rank rather than just a copy of $\mathbb{Z}^{2}$.
--
--   **Formalization note.** $z ^ m$ is the integer power in the group of order isomorphisms. Open intervals are used; if $c = d$ they are empty and the conclusion is vacuous.
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 495, in the proof of Theorem (3.2): "By (1.1a), supp w_n intersect (a_i,b_i) is contained in (c z^n, d z^n). Clearly, the intervals (c z^n, d z^n) are pairwise disjoint subintervals of (a_i,b_i)." PROVENANCE: the paper asserts the disjointness without proof; it is not a numbered result there. Note the source composes maps left to right, so its c z^n is z^n (c) here.

import Mathlib

namespace HomeoLine

theorem pairwise_disjoint_zpow_image {z : ℝ ≃o ℝ} {c d : ℝ} (hcd : c ≤ d) (hz : d < z c) :
    ∀ m n : ℤ, m ≠ n →
      Disjoint (Set.Ioo ((z ^ m) c) ((z ^ m) d)) (Set.Ioo ((z ^ n) c) ((z ^ n) d)) := by
  sorry

end HomeoLine
