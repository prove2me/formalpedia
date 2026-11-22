-- Prove2me | Theorems.Thm_Monotonicity_Theorem_decreasing_extends_to_left_endpoint_closed
-- name    : Monotonicity_Theorem.decreasing_extends_to_left_endpoint_closed
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-12T13:46:19.591713+00:00
-- url     : https://prove2.me/theorems/a2838f01-2d4e-4f0b-b44e-69cad20aa84a
-- title:
--   Strictly decreasing functions extend to a closed left endpoint
-- statement:
--   Gluing a strictly decreasing function to its closed left endpoint.
--
--   Let $f$ be a function defined on a set $I$ of points of a dense linear order without endpoints, and let $s < x_0$ be two values. Suppose every point of $I$ lies in the half-open interval $[s, x_0]$, in the sense that each coordinate equals $s$, lies strictly between $s$ and $x_0$, or equals $x_0$. Suppose further that:
--
--   1. $f$ is strictly decreasing on pairs of points both lying strictly right of $s$;
--   2. for every point $u$ of $I$ strictly right of $s$ but at or left of $x_0$, and every point $y$ of $I$ at $s$, the value $f(u)$ lies strictly below $f(y)$.
--
--   Then
--
--   $$
--   f \text{ is strictly decreasing on all of } I.
--   $$
--
--   This is the left-endpoint mirror of the decreasing right-endpoint gluing lemma, used for the decreasing case of inf-extension arguments: once boundary comparisons at the endpoint $s$ are known (in applications, supplied by continuity at $s$), strict monotonicity on the approaching interval extends to the closed interval.
--
--   **Formalization Note** The boundary hypothesis quantifies over arbitrary points $y$ at $s$ rather than fixing one, so no choice of coordinates is needed.
-- source:
--   Monotonicity theorem assembly (monotonicity.tex), inf-extension uniformity step: extending decreasing behavior from (s, x0] to s

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.decreasing_extends_to_left_endpoint_closed {R : Type}
    (D : DenseLinearOrderNoEndpoints R)
    {I B : Set (Power R 1)}
    (f : {x : Power R 1 // I x} → {y : Power R 1 // B y})
    (s x₀ : R) (hxs : D.lt s x₀)
    (hI : ∀ x : Power R 1, I x → Power.coord1 x = s ∨
      (D.lt s (Power.coord1 x) ∧ D.lt (Power.coord1 x) x₀) ∨ Power.coord1 x = x₀)
    (hleft : ∀ x y (hx : I x) (hy : I y),
      D.lt s (Power.coord1 x) → D.lt s (Power.coord1 y) →
      Lt1 D x y → Lt1 D (f ⟨y, hy⟩).1 (f ⟨x, hx⟩).1)
    (hbound : ∀ u (hu : I u) y (hy : I y),
      (D.lt (Power.coord1 u) x₀ ∨ Power.coord1 u = x₀) →
      D.lt s (Power.coord1 u) → Power.coord1 y = s →
      Lt1 D (f ⟨u, hu⟩).1 (f ⟨y, hy⟩).1) :
    StrictlyDecreasingOn D I B f := by sorry
