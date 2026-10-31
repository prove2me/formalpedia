-- Prove2me | Theorems.Thm_LatentRobust_boundaryRisk_lp_le_l2
-- name    : LatentRobust.boundaryRisk_lp_le_l2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:20:37.196109+00:00
-- url     : https://prove2.me/theorems/d5f26318-b413-43f7-a00d-0f906e82771e
-- title:
--   App. A.3, p.21 — the $\ell_p$ boundary risk at power $\varepsilon_p$ is at most the $\ell_2$ boundary risk at power $\varepsilon_p d^{1/2-1/p}$
-- statement:
--   Let $p\ge2$ and $\varepsilon_p\ge0$, let $P$ be a probability law of $(x,y)$ on $\mathbb R^d\times\mathbb R$, and let $h:\mathbb R^d\to\{+1,-1\}$ be a classifier. Writing $\mathrm{BR}_{\ell_q,\varepsilon}(h)$ for the boundary risk of $h$ against an $\ell_q$ adversary of power $\varepsilon$ under $P$,
--   $$
--   \mathrm{BR}_{\ell_p,\varepsilon_p}(h)\le\mathrm{BR}_{\ell_2,\ \varepsilon_p d^{1/2-1/p}}(h).
--   $$
--
--   This reduces Theorem 3.1 to the case of $\ell_2$ adversaries.
--
--   Differences from the source:
--   - generalization: the Gaussian mixture law (5) → any probability law of (x, y) on ℝ^d × ℝ; reason: the comparison follows from the pointwise inclusion (17); the law (5) is a special case
--   - reading: ‖x‖_{ℓp} = (Σ_i x_i^p)^{1/p} → (Σ_i |x_i|^p)^{1/p}; reason: the standard ℓp norm; without absolute values the expression is not a norm unless p is even
--   - encoding: inf_{‖x′−x‖ ≤ ε} h(x′)y ≤ 0 in the adversarial risk (3) → ∃ x′ with ‖x′ − x‖ ≤ ε and h(x′)y ≤ 0; reason: h is {±1}-valued, so the infimum over the ball is attained
--   - encoding: the adversary's power ε_p, the radius of a ball → 0 ≤ ε; reason: a radius is nonnegative, so no instance of the source is excluded
-- source:
--   Javanmard, Mehrabi, Adversarial robustness for latent models: Revisiting the robust-standard accuracies tradeoff, arXiv:2110.11950v2, App. A.3 (proof of Theorem 3.1), p.21, "More precisely, the boundary risk of ℓp adversaries with power εp will be smaller than ℓ2 adversaries"

import Mathlib
import Definitions.Def_LatentRobust_boundaryRisk

namespace LatentRobust

open MeasureTheory

/-- **`ℓp` versus `ℓ2` boundary risk** (Javanmard, Mehrabi, arXiv:2110.11950v2, App. A.3, p.21): "the boundary risk of
`ℓp` adversaries with power `ε_p` will be smaller than `ℓ2` adversaries with power
`ε_p d^{1/2 − 1/p}`", for `p ≥ 2` and every classifier `h : ℝ^d → {+1, −1}`.

**Formalization Note** Stated for every probability law `P` of `(x, y)` on `ℝ^d × ℝ` (the
paper's setting is the Gaussian mixture law (5), a special case). -/
theorem boundaryRisk_lp_le_l2 {d : ℕ} (P : Measure ((Fin d → ℝ) × ℝ)) [IsProbabilityMeasure P]
    (p εp : ℝ) (hp : 2 ≤ p) (hεp : 0 ≤ εp)
    (h : (Fin d → ℝ) → ℝ) (hh : ∀ x, h x = 1 ∨ h x = -1) :
    boundaryRisk p εp P h ≤ boundaryRisk 2 (εp * (d : ℝ) ^ ((1 : ℝ) / 2 - 1 / p)) P h := by sorry

end LatentRobust
