-- Prove2me | Theorems.Thm_HunterPDE_Newtonian_fundamentalSolution_partial
-- name    : HunterPDE.Newtonian.fundamentalSolution_partial
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:13:55.466411+00:00
-- url     : https://prove2.me/theorems/42aa9de9-b85e-45d8-9cba-37b68bee2250
-- title:
--   Eq. (2.14) — Γ is smooth away from 0 and ∂ᵢΓ(x) = −(1/(nαₙ)) |x|^{1−n} xᵢ/|x|
-- statement:
--   Let $n \ge 2$ and let $\Gamma$ be the fundamental solution (2.12), with $\alpha_n$ the volume of the unit ball. Then $\Gamma$ is infinitely differentiable on $\mathbb{R}^n \setminus \{0\}$, and for every $x \ne 0$ and every $i$,
--   $$\partial_i \Gamma(x) = -\frac{1}{n\alpha_n}\,\frac{1}{|x|^{n-1}}\,\frac{x_i}{|x|}.$$
--   This formula is the basis of every later computation with $\Gamma$: the unit flux (2.15), the local integrability of $D\Gamma$, and the boundary term $\frac1n\delta_{ij}$ in Corollary 2.27.
--
--   **Formalization Note.** Coordinates are 0-based (`i : Fin n`); $\partial_i$ is `fderiv` applied to the basis vector $e_i$. The formula covers both branches of (2.12); for $n = 2$, $\alpha_2 = \pi$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 33, §2.6.1, Eq. (2.14)

import Mathlib
import Definitions.Def_HunterPDE_Newtonian_FundamentalSolution
import Definitions.Def_HunterPDE_Newtonian_PartialDeriv

namespace HunterPDE.Newtonian

open scoped ContDiff

/-- Hunter, *Notes on PDEs*, §2.6.1, p. 33, Eq. (2.14): for `n ≥ 2` the fundamental solution
`Γ` (2.12) is `C^∞` on `ℝⁿ ∖ {0}`, and for `x ≠ 0`
`∂ᵢΓ(x) = −(1/(nαₙ)) · (1/|x|^{n−1}) · (xᵢ/|x|)`. Coordinates are 0-based (`i : Fin n`). -/
theorem fundamentalSolution_partial (n : ℕ) (hn : 2 ≤ n) :
    ContDiffOn ℝ ∞ (fundamentalSolution n) {0}ᶜ ∧
    ∀ (x : EuclideanSpace ℝ (Fin n)), x ≠ 0 → ∀ i : Fin n,
      partialDeriv (fundamentalSolution n) i x =
        -(1 / ((n : ℝ) * unitBallVolume n)) * (1 / ‖x‖ ^ (n - 1)) * (x i / ‖x‖) := by sorry

end HunterPDE.Newtonian
