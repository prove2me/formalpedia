-- Prove2me | Theorems.Thm_GaussMixHH_thm20_kernel_bounds
-- name    : GaussMixHH.thm20_kernel_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:34:17.251194+00:00
-- url     : https://prove2.me/theorems/6ad9143e-89a9-4f9d-a3c1-d66e0e39c197
-- title:
--   Proof of Theorem 20, p.26 — kernel bounds $|K_u(\theta)|\le e^{-\theta^2u}$ and $|\partial_uK_u(\theta)|\le\theta$
-- statement:
--   For $n\in\mathbb N$, $0\le\theta\le1/2$ and $u\ge0$, the kernel $K_u(\theta)=(1-2i\theta)^{-n/2}\exp\big(\frac{i\theta u}{1-2i\theta}\big)$ satisfies
--
--   $$|K_u(\theta)|\le e^{-\theta^2u},\qquad|\partial_uK_u(\theta)|\le\theta,$$
--
--   and these follow from
--
--   $$\operatorname{Re}\frac{i\theta}{1-2i\theta}=-\frac{2\theta^2}{1+4\theta^2}\le-\theta^2,\qquad\Big|\frac{i\theta}{1-2i\theta}\Big|\le\theta,\qquad|(1-2i\theta)^{-n/2}|\le1 .$$
--
--   Close squared radii have close test values, and large squared radii have uniformly small ones; this is what makes a finite grid of radii suffice.
--
--   **Formalization Note** $\partial_u$ is the derivative of the complex-valued function $u\mapsto K_u(\theta)$ of a real variable.
--
--   Differences from the source:
--   - generalization: θ ∈ I = [θ0, q] ⊆ (0, 1/2] → every θ ∈ [0, 1/2]; reason: contains I
--   - encoding: the parenthetical facts → stated as conclusions; reason: they are used later in the proof
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), proof of Theorem 20, "Discretizing the radii", p.26 (PDF p.28)

import Mathlib
import Definitions.Def_GaussMixHH_GridFit

open Complex

namespace GaussMixHH

/-- **Proof of Theorem 20, kernel bounds** (`|K_u(θ)| ≤ e^{−θ²u}`, `|∂_u K_u(θ)| ≤ θ`).

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), proof of Theorem 20, "Discretizing
the radii", p.26 (PDF p.28).

"For θ ∈ I and u ≥ 0, we have |K_u(θ)| ≤ e^{−θ²u}, |∂_uK_u(θ)| ≤ θ. (These follow from
Re(iθ/(1−2iθ)) = −2θ²/(1+4θ²) ≤ −θ², |iθ/(1−2iθ)| ≤ θ, and |(1−2iθ)^{−n/2}| ≤ 1.)"

**Formalization Note.** Generalization: stated for all `0 ≤ θ ≤ 1/2`, which contains
`I = [θ₀, q] ⊆ (0, 1/2]`, every `u ≥ 0` and every `n`. `∂_u K_u(θ)` is the derivative of the
complex-valued function `u ↦ K_u(θ)` of the real variable `u`. The three parenthetical facts are
conclusions too. -/
theorem thm20_kernel_bounds (n : ℕ) (θ u : ℝ) (hθ : 0 ≤ θ) (hθ2 : θ ≤ 1 / 2) (hu : 0 ≤ u) :
    ‖kernelK n u θ‖ ≤ Real.exp (-(θ ^ 2 * u)) ∧
    ‖deriv (fun v : ℝ => kernelK n v θ) u‖ ≤ θ ∧
    (wfun θ).re = -(2 * θ ^ 2) / (1 + 4 * θ ^ 2) ∧
    -(2 * θ ^ 2) / (1 + 4 * θ ^ 2) ≤ -θ ^ 2 ∧
    ‖wfun θ‖ ≤ θ ∧
    ‖gaussFactor n θ‖ ≤ 1 := by sorry

end GaussMixHH
