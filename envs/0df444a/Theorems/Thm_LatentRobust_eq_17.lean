-- Prove2me | Theorems.Thm_LatentRobust_eq_17
-- name    : LatentRobust.eq_17
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:10.353754+00:00
-- url     : https://prove2.me/theorems/67117e97-2840-4b01-b531-f9d0a4768c75
-- title:
--   Display (17) — the $\ell_p$ ball of radius $\varepsilon_p$ lies in the $\ell_2$ ball of radius $\varepsilon_p d^{1/2-1/p}$
-- statement:
--   Let $p\ge2$, $x\in\mathbb R^d$ and $\varepsilon_p\in\mathbb R$. Then
--   $$
--   \{x':\|x'-x\|_{\ell_p}\le\varepsilon_p\}\subseteq B_\varepsilon(x),\qquad \varepsilon=\varepsilon_p\,d^{\frac12-\frac1p},
--   $$
--   where $B_\varepsilon(x)=\{x':\|x'-x\|_{\ell_2}\le\varepsilon\}$ is the closed Euclidean ball.
--
--   It reduces an $\ell_p$ adversary to an $\ell_2$ adversary of larger power, which is the first step of the proof of Theorem 3.1.
--
--   Differences from the source:
--   - reading: ‖x‖_{ℓp} = (Σ_i x_i^p)^{1/p} → (Σ_i |x_i|^p)^{1/p}; reason: the standard ℓp norm; without absolute values the expression is not a norm unless p is even
--   - generalization: adversary power ε_p ≥ 0 and ambient dimension d ≥ 1 → every real ε_p and every d ∈ ℕ; reason: for ε_p < 0 the left side is empty, and the statement for every d specializes to the source's
--   - reading: B_ε(x), the ℓ2-ball centered at x with radius ε → the closed ball {x′ : ‖x′ − x‖_{ℓ2} ≤ ε}; reason: the proof writes ‖x′ − x‖_{ℓ2} ≤ ε
-- source:
--   Javanmard, Mehrabi, Adversarial robustness for latent models: Revisiting the robust-standard accuracies tradeoff, arXiv:2110.11950v2, App. A.3, p.21, eq. (17)

import Mathlib
import Definitions.Def_LatentRobust_lpNorm

namespace LatentRobust

/-- **Display (17)** (Javanmard, Mehrabi, arXiv:2110.11950v2, App. A.3, p.21): for `p ≥ 2`,
`{x′ : ‖x′ − x‖_{ℓp} ≤ ε_p} ⊆ B_ε(x)` with `ε = ε_p d^{1/2 − 1/p}`, where `B_ε(x)` is the
closed `ℓ2` ball of radius `ε` around `x`.

**Formalization Note** The exponent `1/2 − 1/p` is a real number and `d^{1/2−1/p}` is a real
power. The statement is for every `d`, every `x ∈ ℝ^d` and every real `ε_p`. -/
theorem eq_17 {d : ℕ} (p εp : ℝ) (hp : 2 ≤ p) (x : Fin d → ℝ) :
    {x' : Fin d → ℝ | lpNorm p (x' - x) ≤ εp} ⊆
      {x' : Fin d → ℝ | lpNorm 2 (x' - x) ≤ εp * (d : ℝ) ^ ((1 : ℝ) / 2 - 1 / p)} := by sorry

end LatentRobust
