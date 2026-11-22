-- Prove2me | Theorems.Thm_KarimiPL_RCD_expected_cdStep_contraction
-- name    : KarimiPL.RCD.expected_cdStep_contraction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:55.872233+00:00
-- url     : https://prove2.me/theorems/f1a4e177-6f27-4174-84ec-15331f694bd8
-- title:
--   Proof of Theorem 3, p. 5 — one-step expected gap contraction
-- statement:
--   Let $d\ge1$, $L>0$, and let $f$ obey the coordinate-wise upper bound (5). Suppose $x^*$ is a global minimizer, $f^*=f(x^*)$, and $f$ satisfies the Polyak–Łojasiewicz (PL) inequality $\frac12\|\nabla f(x)\|^2\ge\mu(f(x)-f^*)$ for some $\mu>0$. If $I$ is uniform over the $d$ coordinates, then for every $x$,
--
--   $$
--   \mathbb E_I[f(T_I(x))-f^*]
--   \le\left(1-\frac\mu{dL}\right)(f(x)-f^*).
--   $$
--
--   This is the conditional one-step contraction used in Theorem 3. The minimizer fixes the optimal value; it is not an independently chosen lower bound.
--
--   **Formalization Note** The published PL predicate is written with both sides multiplied by two. The expectation is an explicit finite average.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, proof of Theorem 3, final displayed inequality, p. 5

import Mathlib
import Definitions.Def_KarimiPL_RCD_Setting
import Definitions.Def_ShiOptrates_FunctionClass

namespace KarimiPL.RCD

/-- Conditional expected contraction in the proof of Theorem 3, p. 5. -/
theorem expected_cdStep_contraction {d : ℕ} (hd : 0 < d)
    (f : KarimiPL.Rel.E d → ℝ) (L : ℝ) (hL : 0 < L) (hcoord : CoordLipschitz f L)
    (xstar : KarimiPL.Rel.E d) (hxstar : ∀ y, f xstar ≤ f y)
    (mu : ℝ) (hmu : 0 < mu)
    (hPL : ShiOptRates.PolyakLojasiewicz f (gradient f) mu (f xstar)) :
    ∀ x : KarimiPL.Rel.E d,
      (1 / (d : ℝ)) * ∑ i : Fin d, (f (cdStep f L x i) - f xstar) ≤
        (1 - mu / ((d : ℝ) * L)) * (f x - f xstar) := by sorry

end KarimiPL.RCD
