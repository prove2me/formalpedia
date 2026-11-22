-- Prove2me | Theorems.Thm_KarimiPL_RCD_expected_cdStep_decrease
-- name    : KarimiPL.RCD.expected_cdStep_decrease
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:54.764122+00:00
-- url     : https://prove2.me/theorems/b09c309d-633d-4e81-bbe9-e15e5da166e5
-- title:
--   Proof of Theorem 3, p. 5 — uniform expected decrease
-- statement:
--   Let $d\ge1$ and suppose $f:\mathbb R^d\to\mathbb R$ obeys (5) with $L>0$. Draw one coordinate $I$ uniformly from the $d$ coordinates and set $x^+=T_I(x)$. For every $x$,
--
--   $$
--   \mathbb E_I[f(x^+)]
--   =\frac1d\sum_{i=1}^d f(T_i(x))
--   \le f(x)-\frac1{2dL}\|\nabla f(x)\|^2.
--   $$
--
--   The averaged decrease relates a random coordinate update to the full gradient norm. It is the middle displayed chain in the proof of Theorem 3.
--
--   **Formalization Note** The expectation is a finite average; $d\ge1$ makes the uniform distribution well defined.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, proof of Theorem 3, expected-decrease display, p. 5

import Mathlib
import Definitions.Def_KarimiPL_RCD_Setting

namespace KarimiPL.RCD

/-- Uniformly averaged decrease in the proof of Theorem 3, p. 5. -/
theorem expected_cdStep_decrease {d : ℕ} (hd : 0 < d) (f : KarimiPL.Rel.E d → ℝ) (L : ℝ)
    (hL : 0 < L) (hcoord : CoordLipschitz f L) :
    ∀ x : KarimiPL.Rel.E d,
      (1 / (d : ℝ)) * ∑ i : Fin d, f (cdStep f L x i) ≤
        f x - 1 / (2 * (d : ℝ) * L) * ‖gradient f x‖ ^ 2 := by sorry

end KarimiPL.RCD
