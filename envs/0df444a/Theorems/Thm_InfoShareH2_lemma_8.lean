-- Prove2me | Theorems.Thm_InfoShareH2_lemma_8
-- name    : InfoShareH2.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:44.149275+00:00
-- url     : https://prove2.me/theorems/fc0d5848-a0eb-463c-8eda-7ff3922d8d15
-- title:
--   Lemma 8 — $\lim_{r\to0^+}\int_{C_r(z_0,\theta_1,\theta_2)}f(z)\,dz=-i(\theta_2-\theta_1)c$
-- statement:
--   Let $z_0,c\in\mathbb C$, $\theta_1\le\theta_2\le\theta_1+2\pi$, and let $C_r=\{z_0+re^{-i\lambda}:\lambda\in[\theta_1,\theta_2]\}$. Let $f:\mathbb C\to\mathbb C$ satisfy: for every $\varepsilon>0$ there is $\delta>0$ such that $|(z-z_0)f(z)-c|<\varepsilon$ for all $0<r<\delta$ and all $z\in C_r$. Suppose the arc integrals $\int_{C_r}f(z)\,dz$ exist for small $r>0$. Then
--
--   $$\lim_{r\to0^+}\int_{C_r}f(z)\,dz=-i(\theta_2-\theta_1)\,c.$$
--
--   The arc is traversed through the parametrization $z=z_0+re^{-i\lambda}$, $\lambda$ from $\theta_1$ to $\theta_2$, so $dz=-ire^{-i\lambda}d\lambda$.
--
--   The lemma evaluates the contribution of the boundary pole $z=1$ in the contour arguments of Lemma 3 and Theorem 2.
--
--   Differences from the source:
--   - reading: ∫_{C_r} f(z)dz (taken as existing) → for all small r > 0 the parametrized integrand is interval integrable on [θ₁, θ₂]; reason: the source writes the integrals as existing; in Lean a non-integrable integrand integrates to 0
--   - encoding: contour integral over C_r(z₀, θ₁, θ₂) → ∫_{θ₁}^{θ₂} f(z₀ + re^{−iλ})·(−i r e^{−iλ}) dλ; reason: the parametrization of the proof
-- source:
--   Caldentey–Giloni–Hurvich–Zhang, Information Design and Sharing in Supply Chains, SSRN 4319721 (v. 2024-01-20), https://ssrn.com/abstract=4319721, Lemma 8, p.51

import Mathlib
import Definitions.Def_InfoShareH2_Model

open Filter Topology MeasureTheory Complex

set_option autoImplicit false

namespace InfoShareH2

/-- **Lemma 8 (arc integral around a simple pole).**
SSRN 4319721 (v. 2024-01-20), Lemma 8, p.51. "Define
`C_r(z_0, θ_1, θ_2) = {z_0 + re^{−iλ} : λ ∈ [θ_1, θ_2]}` where `0 ≤ θ_2 − θ_1 ≤ 2π`. Let `f(z)` be a
function such that for any `ε > 0`, there exists some `δ > 0` such that for all `0 < r < δ`,
`|(z − z_0)f(z) − c| < ε` for all `z ∈ C_r(z_0, θ_1, θ_2)`. Then
`lim_{r→0+} ∫_{C_r(z_0,θ_1,θ_2)} f(z)dz = −i(θ_2 − θ_1)c`."

**Formalization Note** The arc integral is written through the parametrization of the proof,
`z = z_0 + re^{−iλ}`, `dz = −i r e^{−iλ} dλ`. The source takes the arc integrals as existing; the
hypothesis `hint` says so for all small `r` (otherwise Lean's integral of a non-integrable function
is `0`). -/
theorem lemma_8 (f : ℂ → ℂ) (z0 c : ℂ) (θ1 θ2 : ℝ) (h12 : 0 ≤ θ2 - θ1)
    (h12' : θ2 - θ1 ≤ 2 * Real.pi)
    (hf : ∀ e > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ r : ℝ, 0 < r → r < δ → ∀ lam ∈ Set.Icc θ1 θ2,
      ‖((z0 + (r : ℂ) * exp (-(lam : ℂ) * I)) - z0) * f (z0 + (r : ℂ) * exp (-(lam : ℂ) * I)) - c‖ < e)
    (hint : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun lam : ℝ => f (z0 + (r : ℂ) * exp (-(lam : ℂ) * I)) * (-I * (r : ℂ) * exp (-(lam : ℂ) * I)))
      volume θ1 θ2) :
    Tendsto (fun r : ℝ => ∫ lam in θ1..θ2,
        f (z0 + (r : ℂ) * exp (-(lam : ℂ) * I)) * (-I * (r : ℂ) * exp (-(lam : ℂ) * I)))
      (𝓝[>] (0 : ℝ)) (𝓝 (-I * ((θ2 - θ1 : ℝ) : ℂ) * c)) := by sorry

end InfoShareH2
