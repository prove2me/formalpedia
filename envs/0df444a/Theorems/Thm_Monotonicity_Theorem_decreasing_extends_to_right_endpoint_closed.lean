-- Prove2me | Theorems.Thm_Monotonicity_Theorem_decreasing_extends_to_right_endpoint_closed
-- name    : Monotonicity_Theorem.decreasing_extends_to_right_endpoint_closed
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-12T13:26:54.735581+00:00
-- url     : https://prove2.me/theorems/3375e336-7e05-49c5-a5ef-cedee092cb41
-- title:
--   Strictly decreasing functions extend to a closed right endpoint
-- statement:
--   Gluing a strictly decreasing function to its closed right endpoint.
--
--   Let $f$ be a function defined on a set $I$ of points of a dense linear order without endpoints, and let $x_0 < s$ be two values. Suppose every point of $I$ lies in the half-open interval $[x_0, s]$, in the sense that each coordinate equals $x_0$, lies strictly between $x_0$ and $s$, or equals $s$. Suppose further that:
--
--   1. $f$ is strictly decreasing on pairs of points both lying strictly left of $s$;
--   2. for every point $u$ of $I$ at or right of $x_0$ but strictly left of $s$, and every point $y$ of $I$ at $s$, the value $f(y)$ lies strictly below $f(u)$.
--
--   Then
--
--   $$
--   f \text{ is strictly decreasing on all of } I.
--   $$
--
--   This is the exact mirror of the increasing endpoint-gluing lemma, used for the decreasing case of sup-extension arguments: once boundary comparisons at the endpoint $s$ are known (in applications, supplied by continuity at $s$), strict monotonicity on the approaching interval extends to the closed interval.
--
--   **Formalization Note** The boundary hypothesis quantifies over arbitrary points $y$ at $s$ rather than fixing one, so no choice of coordinates is needed. This version supersedes an earlier draft whose boundary hypothesis missed the left-endpoint pair.
-- source:
--   Monotonicity theorem assembly (monotonicity.tex), sup-extension uniformity step: extending decreasing behavior from [x0, s) to s

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.decreasing_extends_to_right_endpoint_closed {R : Type}
    (D : DenseLinearOrderNoEndpoints R)
    {I B : Set (Power R 1)}
    (f : {x : Power R 1 // I x} → {y : Power R 1 // B y})
    (x₀ s : R) (hxs : D.lt x₀ s)
    (hI : ∀ x : Power R 1, I x → Power.coord1 x = x₀ ∨
      (D.lt x₀ (Power.coord1 x) ∧ D.lt (Power.coord1 x) s) ∨ Power.coord1 x = s)
    (hleft : ∀ x y (hx : I x) (hy : I y),
      D.lt (Power.coord1 x) s → D.lt (Power.coord1 y) s →
      Lt1 D x y → Lt1 D (f ⟨y, hy⟩).1 (f ⟨x, hx⟩).1)
    (hbound : ∀ u (hu : I u) y (hy : I y),
      (Power.coord1 u = x₀ ∨ D.lt x₀ (Power.coord1 u)) →
      D.lt (Power.coord1 u) s → Power.coord1 y = s →
      Lt1 D (f ⟨y, hy⟩).1 (f ⟨u, hu⟩).1) :
    StrictlyDecreasingOn D I B f := by sorry
