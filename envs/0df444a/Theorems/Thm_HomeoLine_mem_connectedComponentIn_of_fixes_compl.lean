-- Prove2me | Theorems.Thm_HomeoLine_mem_connectedComponentIn_of_fixes_compl
-- name    : HomeoLine.mem_connectedComponentIn_of_fixes_compl
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-13T07:40:09.69431+00:00
-- url     : https://prove2.me/theorems/8628a5ae-d11e-4804-95a3-37f80f3a179c
-- title:
--   A homeomorphism fixing the complement of an open set preserves its components
-- statement:
--   Let $h$ be an order isomorphism of $\mathbb{R}$ that fixes every point outside a set $U$, and let $x \in U$. Then $h(x)$ lies in the same connected component of $U$ as $x$:
--
--   $$h(x) \in \mathrm{connectedComponentIn}\ U\ x .$$
--
--   So such a map cannot carry a point of $U$ into a different component — it permutes nothing, and each component is invariant.
--
--   Two observations give this. First, $h$ cannot push a point out of $U$: if $h(x) \notin U$ then $h$ fixes $h(x)$, so $h(h(x)) = h(x)$ and injectivity gives $h(x) = x$, contradicting $x \in U$. Second, the whole segment between $x$ and $h(x)$ lies in $U$: a point $y$ of that segment outside $U$ would be fixed, and monotonicity then squeezes $y$ onto $h(x)$, which is in $U$. That segment is connected, contains both points, and lies in $U$, so both points share a component.
--
--   **Role.** The invariance that makes "the number of components of $U$ that a map's moved set meets" a usable quantity: conjugating by a map supported in $U$ cannot change which components are met. On the line this is what replaces a general orientation or ordering argument.
--
--   **Formalization note.** No openness of $U$ is assumed; the segment argument needs only that $h$ is increasing and fixes the complement pointwise.
-- source:
--   Standard; on the line this is the observation that a monotone map fixing the complement of a set cannot permute that set's components. Used at M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 495, in the proof of Theorem (3.2), where it is the unstated reason the conjugating word z preserves each component of supp f union supp g, so that the conjugates of w meet the same components. PROVENANCE: not stated as a numbered result there.

import Mathlib

namespace HomeoLine

theorem mem_connectedComponentIn_of_fixes_compl {h : ℝ ≃o ℝ} {U : Set ℝ}
    (hfix : ∀ y, y ∉ U → h y = y) {x : ℝ} (hx : x ∈ U) :
    h x ∈ connectedComponentIn U x := by
  sorry

end HomeoLine
