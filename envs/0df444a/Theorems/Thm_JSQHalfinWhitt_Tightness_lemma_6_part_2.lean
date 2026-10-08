-- Prove2me | Theorems.Thm_JSQHalfinWhitt_Tightness_lemma_6_part_2
-- name    : JSQHalfinWhitt.Tightness.lemma_6_part_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:43:55.493829+00:00
-- url     : https://prove2.me/theorems/00b52ac9-2e5e-430a-8e20-087cfb670a03
-- title:
--   Lemma 6, part 2 — for $\kappa > \beta$, $\tau$ is differentiable on $x \ge \Gamma^{(\kappa)}$ with $\tau_1 \le 0$, $\tau_2 = \tau_1\tau \le 0$ (4.12)
-- statement:
--   Let $n \ge 1$, $0 < \beta < \sqrt n$ and $\kappa > \beta$, and let $\tau$ be the hitting time of Lemma 6 and $\nu^*$ the function of Lemma 5. At every point $x$ with $x_1 \le 0$ and $x \ge \Gamma^{(\kappa)}$ (that is, $x_2 \ge \nu^*(x_1)$), $\tau(x)$ is finite and $\tau$ is differentiable, with
--   $$\tau_1(x) = -\frac{e^{-\tau(x)}}{x_2 e^{-\tau(x)} - \beta/\sqrt n} \le 0,\qquad \tau_2(x) = \tau_1(x)\tau(x) \le 0, \tag{4.12}$$
--   where $\tau_1(x)$ is the left derivative when $x_1 = 0$.
--
--   These derivative formulas give the first and second partial derivatives of the upper branch of $f^*$ in (4.14), and through them the bounds (3.9)–(3.11).
--
--   **Formalization Note** Differentiability is stated along each coordinate: in $x_1$ as a derivative within $(-\infty, 0]$ (two-sided for $x_1 < 0$, from the left at $x_1 = 0$), in $x_2$ as a two-sided derivative. The derivatives are of `tauR`, the real value of $\tau$, which is evaluated near points where $\tau$ is finite. The formula is stated as the value of the derivative together with the two sign conditions.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), p. 13, Lemma 6, part 2, (4.12)

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Fluid

namespace JSQHalfinWhitt.Tightness

/-- Lemma 6, part 2 (Braverman, p. 13): if `κ > β`, then `τ` is finite and differentiable at every
`x ≥ Γ^{(κ)}` (i.e. `x_1 ≤ 0`, `x_2 ≥ ν^*(x_1)`), with
`τ_1(x) = −e^{−τ(x)}/(x_2 e^{−τ(x)} − β/√n) ≤ 0` and `τ_2(x) = τ_1(x) τ(x) ≤ 0` (4.12); `τ_1` is
the left derivative when `x_1 = 0`. -/
theorem lemma_6_part_2 (n : ℕ) (β κ : ℝ) (hn : 1 ≤ n) (hβ : 0 < β) (hβn : β < Real.sqrt n)
    (hκ : β < κ) (x : ℝ × ℝ) (hx1 : x.1 ≤ 0) (hxΓ : nuStar β κ n x.1 ≤ x.2) :
    ∃ t : ℝ, tau β n x = t ∧
      HasDerivWithinAt (fun s => tauR β n (s, x.2))
        (-(Real.exp (-t) / (x.2 * Real.exp (-t) - β / Real.sqrt n))) (Set.Iic 0) x.1 ∧
      HasDerivAt (fun s => tauR β n (x.1, s))
        (-(Real.exp (-t) / (x.2 * Real.exp (-t) - β / Real.sqrt n)) * t) x.2 ∧
      -(Real.exp (-t) / (x.2 * Real.exp (-t) - β / Real.sqrt n)) ≤ 0 ∧
      -(Real.exp (-t) / (x.2 * Real.exp (-t) - β / Real.sqrt n)) * t ≤ 0 := by sorry

end JSQHalfinWhitt.Tightness
