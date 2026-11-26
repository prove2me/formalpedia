-- Prove2me | Theorems.Thm_LefebvreVariations_sendov_degree_three
-- name    : LefebvreVariations.sendov_degree_three
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:18:14.615596+00:00
-- url     : https://prove2.me/theorems/4ca21979-b599-5c86-9a64-934b482043f4
-- title:
--   Lefebvre's variations, No. 148 — on a theme by Sendov: Sendov's conjecture holds in degree 3
-- statement:
--   Let $p\in\mathbb{C}[X]$ have degree exactly $3$, with all its roots in the closed unit disc, and let $z_0$ be a root of $p$. Then $p'$ has a root $w$ with
--   $$
--   |w-z_0|\le 1 .
--   $$
--
--   This is Sendov's conjecture (also called the Ilieff–Sendov conjecture) restricted to degree $3$. The conjecture is open in general; the degrees $3,4,5$ were settled in the late 1960s, degrees $6$ and $7$ by Borcea in the 1990s.
--
--   **Formalization Note** The statement is that of the platform's `sendov_conjecture` with the hypothesis `2 ≤ p.natDegree` replaced by `p.natDegree = 3`. Roots are taken in $\mathbb{C}$ via `IsRoot`; `p ≠ 0` follows from the degree.
--
--   **Why this is a variation.** Variation on the open platform theorem sendov_conjecture: the parent's statement for degree exactly 3, the first sizes after the trivial degree 2 (where the critical point is the midpoint of the two roots). A finite-dimensional statement in the coefficients.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Sendov's conjecture, listed in W. K. Hayman, Research Problems in Function Theory (1967), as I recall Problem 4.5 (cited from memory); the degree-3 case: Rubinstein and others, late 1960s (degree 3); exact attributions cited from memory. Degrees 6 and 7 by J. Borcea (1996 and later). A web search confirmed the general picture (degrees 3-5 settled in quick succession in the late 1960s; degree 6 by Borcea 1996; degree 7 by Borcea) but not the individual authors. Truth check: 100000 random polynomials of degree 3 with roots in the unit disc (including many with roots on the circle) gave a largest distance 'root of p to nearest root of p'' of 0.980 < 1.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

theorem sendov_degree_three (p : Polynomial ℂ) (hdeg : p.natDegree = 3)
    (hroots : ∀ z : ℂ, p.IsRoot z → ‖z‖ ≤ 1)
    (z₀ : ℂ) (hz₀ : p.IsRoot z₀) :
    ∃ w : ℂ, p.derivative.IsRoot w ∧ ‖w - z₀‖ ≤ 1 := by
  sorry

end LefebvreVariations
