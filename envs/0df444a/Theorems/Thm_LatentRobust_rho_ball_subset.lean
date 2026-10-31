-- Prove2me | Theorems.Thm_LatentRobust_rho_ball_subset
-- name    : LatentRobust.rho_ball_subset
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:16.517055+00:00
-- url     : https://prove2.me/theorems/fb603c14-f868-42d3-88a8-59142f8dc669
-- title:
--   App. A.3, p.21 — $\rho(B_\varepsilon(x))\subseteq B_{\varepsilon/c}(\rho(x))$ for $\rho=\varphi^{-1}$
-- statement:
--   Let $c>0$ and let $\varphi:\mathbb R\to\mathbb R$ be differentiable with $\varphi'(t)\ge c$ for all $t$, and let $\rho=\varphi^{-1}$ act entrywise on $\mathbb R^d$. For every $x\in\mathbb R^d$ and every radius $\varepsilon$,
--   $$
--   \rho\big(B_\varepsilon(x)\big)\subseteq B_{\varepsilon/c}\big(\rho(x)\big),
--   $$
--   where $B_r(u)$ is the closed Euclidean ball of radius $r$ around $u$.
--
--   It transfers an $\ell_2$ perturbation of the feature to a perturbation of the latent preimage, at the cost of the factor $1/c$.
--
--   Differences from the source:
--   - generalization: a radius ε ≥ 0 (adversary power) → any real ε; reason: for ε < 0 the ball is empty
--   - encoding: φ⁻¹ applied entrywise → Function.invFun φ applied entrywise; reason: under φ' ≥ c > 0, φ is a bijection of ℝ and invFun φ is its inverse
--   - reading: B_ε(x), the ℓ2-ball → the closed ball {x′ : ‖x′ − x‖_{ℓ2} ≤ ε}; reason: the proof writes ‖x′ − x‖ ≤ ε
-- source:
--   Javanmard, Mehrabi, Adversarial robustness for latent models: Revisiting the robust-standard accuracies tradeoff, arXiv:2110.11950v2, App. A.3 (proof of Theorem 3.1), p.21, "ρ (Bε(x)) is a subset of Bε/c(ρ(x))"

import Mathlib
import Definitions.Def_LatentRobust_lpNorm

namespace LatentRobust

/-- **`ρ(B_ε(x)) ⊆ B_{ε/c}(ρ(x))`** (Javanmard, Mehrabi, arXiv:2110.11950v2, App. A.3, p.21): if `φ : ℝ → ℝ` has
derivative `dφ/dt ≥ c` for a constant `c > 0` and `ρ = φ⁻¹` acts entrywise, then `ρ` maps
the closed `ℓ2` ball of radius `ε` around `x ∈ ℝ^d` into the closed `ℓ2` ball of radius
`ε/c` around `ρ(x)`.

**Formalization Note** `φ⁻¹` is `Function.invFun φ`; under the hypotheses `φ` is a bijection of
`ℝ` and `invFun φ` is its inverse. -/
theorem rho_ball_subset {d : ℕ} (φ : ℝ → ℝ) (c : ℝ) (hc : 0 < c) (hφ : Differentiable ℝ φ)
    (hφc : ∀ t, c ≤ deriv φ t) (x : Fin d → ℝ) (ε : ℝ) :
    (fun u : Fin d → ℝ => fun i => Function.invFun φ (u i)) ''
        {x' : Fin d → ℝ | lpNorm 2 (x' - x) ≤ ε} ⊆
      {v : Fin d → ℝ | lpNorm 2 (v - fun i => Function.invFun φ (x i)) ≤ ε / c} := by sorry

end LatentRobust
