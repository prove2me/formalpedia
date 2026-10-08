-- Prove2me | Theorems.Thm_JSQHalfinWhitt_Tightness_lemma_5
-- name    : JSQHalfinWhitt.Tightness.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:31.708984+00:00
-- url     : https://prove2.me/theorems/8d9438de-9193-44a5-8bef-c6f0003ff3c8
-- title:
--   Lemma 5 — the system (4.8) has exactly one solution $(\nu^*(x_1), \eta^*(x_1))$, and $\gamma^{(\kappa)}(x_1) \subset \Gamma^{(\kappa)}$
-- statement:
--   Let $n \ge 1$ and $0 < \beta < \sqrt n$. Fix $\kappa \ge \beta$. For every $x_1 \le 0$, the nonlinear system in $(\nu, \eta)$
--   $$-\beta/\sqrt n + (x_1 + \beta/\sqrt n)e^{-\eta} + \eta\nu e^{-\eta} = 0,\qquad \nu e^{-\eta} = \kappa/\sqrt n,\qquad \nu \ge \kappa/\sqrt n,\quad \eta \ge 0 \tag{4.8}$$
--   has exactly one solution $(\nu^*(x_1), \eta^*(x_1))$. Moreover, with the curve $\Gamma^{(\kappa)} = \{x \in \Omega \mid x_2 = \nu^*(x_1)\}$ and the arc
--   $$\gamma^{(\kappa)}(x_1) = \Big\{\big(-\beta/\sqrt n + (x_1 + \beta/\sqrt n)e^{-t} + t\nu^*(x_1)e^{-t},\ \nu^*(x_1)e^{-t}\big) \ \Big|\ t \in [0, \eta^*(x_1)]\Big\},$$
--   one has $\gamma^{(\kappa)}(x_1) \subset \Gamma^{(\kappa)}$ for every $x_1 \le 0$.
--
--   $\Gamma^{(\kappa)}$ is the set of initial conditions whose linear fluid path first meets the vertical axis at $(0, \kappa/\sqrt n)$, and the second statement says that this curve is invariant along those paths. It separates the regions in which the Lyapunov function $f^*$ of (4.14) takes different forms.
--
--   **Formalization Note** The first conclusion is the existence and uniqueness for each $x_1 \le 0$; `nuStar`, `etaStar` are defined as the components of that unique solution. The inclusion $\gamma^{(\kappa)}(x_1) \subset \Gamma^{(\kappa)}$ includes that every point of the arc lies in $\Omega$ (first coordinate $\le 0$, second $\ge 0$); this is part of the claim, not an assumption. The Halfin–Whitt standing assumptions $\beta > 0$, $\beta < \sqrt n$ are hypotheses.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), p. 12, Lemma 5, (4.8)

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Fluid

namespace JSQHalfinWhitt.Tightness

/-- Lemma 5 (Braverman, p. 12): for `κ ≥ β` and every `x_1 ≤ 0`, the system (4.8) has exactly one
solution `(ν^*(x_1), η^*(x_1))`; and for every `x_1 ≤ 0` the arc `γ^{(κ)}(x_1)` lies on the curve
`Γ^{(κ)} = {x ∈ Ω | x_2 = ν^*(x_1)}` (in particular every point of the arc lies in `Ω`). -/
theorem lemma_5 (n : ℕ) (β κ : ℝ) (hn : 1 ≤ n) (hβ : 0 < β) (hβn : β < Real.sqrt n)
    (hκ : β ≤ κ) :
    (∀ x1 : ℝ, x1 ≤ 0 → ∃! p : ℝ × ℝ, FluidSystem β κ n x1 p.1 p.2) ∧
      ∀ x1 : ℝ, x1 ≤ 0 → gammaArc β κ n x1 ⊆ gammaCurve β κ n := by sorry

end JSQHalfinWhitt.Tightness
