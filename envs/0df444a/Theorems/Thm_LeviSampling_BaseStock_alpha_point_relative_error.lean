-- Prove2me | Theorems.Thm_LeviSampling_BaseStock_alpha_point_relative_error
-- name    : LeviSampling.BaseStock.alpha_point_relative_error
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:00.673595+00:00
-- url     : https://prove2.me/theorems/aed9379f-76f8-484e-8bf7-857d39ff7c18
-- title:
--   Lemma 3.3 — an α-point is (1 + ε)-optimal
-- statement:
--   Let $f : \mathbb R \to \mathbb R$ be convex with a global minimum at $y^*$. Suppose that for some $h, b > 0$ and $d \in \mathbb R$,
--   $$f(y) \ge h(y - d)^+ + b(d - y)^+ \quad \text{for all } y .$$
--   Let $0 < \varepsilon \le 1$ and $\alpha = (\varepsilon/3)\min(b, h)$. If $\hat y$ is an $\alpha$-point of $f$, then
--   $$f(\hat y) \le (1 + \varepsilon)\, f(y^*).$$
--   This converts first-order information (a small subgradient) into a relative-error guarantee; in the paper it is applied to the shadow cost $\tilde U_t$, whose newsvendor part provides the piecewise-linear lower bound.
-- source:
--   Levi, Roundy & Shmoys, Provably Near-Optimal Sampling-Based Policies for Stochastic Inventory Control Models, Math. Oper. Res. 32(4) 2007, p. 833, Lemma 3.3

import Mathlib
import Definitions.Def_LeviSampling_BaseStock_AlphaPoint

namespace LeviSampling.BaseStock

/-- **Lemma 3.3** (Levi, Roundy & Shmoys 2007, p. 833). Let `f : ℝ → ℝ` be convex with a minimum
at `y*`, and suppose `f(y) ≥ h (y - d)⁺ + b (d - y)⁺` for all `y`, where `h, b > 0`. Let
`0 < ε ≤ 1` and `α = (ε/3) min(b, h)`. If `ŷ` is an `α`-point of `f`, then
`f(ŷ) ≤ (1 + ε) f(y*)`. -/
theorem alpha_point_relative_error (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (ystar : ℝ)
    (hmin : ∀ y, f ystar ≤ f y) (h b d : ℝ) (hh : 0 < h) (hb : 0 < b)
    (hlow : ∀ y, h * max (y - d) 0 + b * max (d - y) 0 ≤ f y)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (yhat : ℝ)
    (hα : IsAlphaPoint f (ε / 3 * min b h) yhat) :
    f yhat ≤ (1 + ε) * f ystar := by sorry

end LeviSampling.BaseStock
