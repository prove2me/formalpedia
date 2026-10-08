-- Prove2me | Theorems.Thm_JSQHalfinWhitt_Tightness_lemma_6_eq_4_10
-- name    : JSQHalfinWhitt.Tightness.lemma_6_eq_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:13.109893+00:00
-- url     : https://prove2.me/theorems/b7acc230-3275-4bcb-96d5-f0e5074bc1d2
-- title:
--   Lemma 6, (4.10) — $\tau(0, x_2) = 0$ for $x_2 \ge 0$
-- statement:
--   Let $n \ge 1$ and $0 < \beta < \sqrt n$. For $x = (x_1, x_2)$ let $\tau(x)$ be the smallest solution $\eta \ge 0$ of
--   $$\beta/\sqrt n - (x_1 + \beta/\sqrt n)e^{-\eta} - \eta x_2 e^{-\eta} = 0,$$
--   and $\tau(x) = \infty$ if no solution exists. Then
--   $$\tau(0, x_2) = 0,\qquad x_2 \ge 0. \tag{4.10}$$
--
--   $\tau(x)$ is the time at which the fluid path started at $x$ first hits the vertical axis; (4.10) says that a path started on the axis is there at time $0$.
--
--   **Formalization Note** $\tau$ takes values in `WithTop ℝ` ($\infty$ is `⊤`). The paper defines $\tau$ for $x \in (-\infty,0]\times[\kappa/\sqrt n,\infty)$ but states (4.10) for all $x_2 \ge 0$; the defining formula is used at every $x$, so (4.10) is stated for all $x_2 \ge 0$ as printed.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), p. 13, Lemma 6, (4.10)

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Fluid

namespace JSQHalfinWhitt.Tightness

/-- Lemma 6, (4.10) (Braverman, p. 13): `τ(0, x_2) = 0` for every `x_2 ≥ 0`. -/
theorem lemma_6_eq_4_10 (n : ℕ) (β : ℝ) (hn : 1 ≤ n) (hβ : 0 < β) (hβn : β < Real.sqrt n)
    (x2 : ℝ) (hx2 : 0 ≤ x2) :
    tau β n (0, x2) = 0 := by sorry

end JSQHalfinWhitt.Tightness
