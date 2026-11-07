-- Prove2me | Theorems.Thm_GaussMixHH_thm20_grid
-- name    : GaussMixHH.thm20_grid
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:34:22.849299+00:00
-- url     : https://prove2.me/theorems/f101de16-5869-4183-8ffe-13c43a62c840
-- title:
--   Proof of Theorem 20, pp.26–27 — grid approximation: $P\rho$ has the same near mass and $\sup_{\theta\in I}|\Phi_\rho-\Phi_{P\rho}|\le\xi$
-- statement:
--   There is a universal constant $C>0$ such that the following holds. Let $n\in\mathbb N$, $R>0$, $0<\theta_0\le q\le1/2$ (so $I=[\theta_0,q]\subseteq(0,1/2]$), $\xi>0$, and
--
--   $$U=\max\{R^2,\theta_0^{-2}\log(8/\xi)\},\qquad s=\frac{\xi}{4q}.$$
--
--   1. There is a grid of mesh at most $s$ on $[0,R^2/4]$ and on $[R^2,U]$, endpoints included, with $M=|U|\le C\big(1+q(R^2/4+U-R^2)/\xi\big)$ points.
--   2. Every such grid admits a rounding map $P$: each squared radius of $[0,R^2/4]$ or $[R^2,U]$ goes to a grid point of its own interval within $s$, and every $u>U$ goes to $U$.
--   3. For every such grid and rounding map and every $(R/2,R)$-gapped radial probability distribution $\rho$, the rounded distribution $P\rho$ (a probability vector on the grid) has exactly the near mass of $\rho$, and
--   $$\sup_{\theta\in I}|\Phi_\rho(\theta)-\Phi_{P\rho}(\theta)|\le\xi .$$
--
--   A finite grid therefore approximates the expected test values of every allowed radial distribution, including ones of unbounded support. In the paper $\xi=\Gamma/1000$.
--
--   Differences from the source:
--   - generalization: the parameters of the proof (ξ = Γ/1000, θ0, q from Proposition 19, 0 < R ≤ 1) → any R > 0, 0 < θ₀ ≤ q ≤ 1/2, ξ > 0; reason: the argument uses only these ranges; the proof's values are a special case
--   - generalization: the rounding procedure P → every measurable rounding map with the stated properties; reason: the paper's procedure is such a map
--   - reading: "take grids of mesh at most s … including all endpoints" and "The mesh gives M ≤ C(1 + q(R²/4 + U − R²)/ξ)" → existence of such a grid with the size bound, existence of a rounding map for each grid; reason: the construction the proof takes as available
--   - encoding: mesh at most s → endpoints in the grid and every point of the interval bracketed by two grid points of it at most s apart; reason: equivalent to all consecutive gaps being at most s
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), proof of Theorem 20, pp.26–27 (PDF pp.28–29)

import Mathlib
import Definitions.Def_GaussMixHH_RadialTransform
import Definitions.Def_GaussMixHH_Gapped
import Definitions.Def_GaussMixHH_GridFit

open MeasureTheory Complex

namespace GaussMixHH

/-- **Proof of Theorem 20, grid approximation** (`Pρ` has the same near mass and
`sup_{θ∈I} |Φ_ρ(θ) − Φ_{Pρ}(θ)| ≤ ξ`; `M ≤ C(1 + q(R²/4 + U − R²)/ξ)`).

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), proof of Theorem 20, pp.26–27
(PDF pp.28–29).

"Let ξ = Γ/1000, U = max{R², θ0^{−2} log(8/ξ)}, s = ξ/(4q), and take grids of mesh at most s on
[0, R²/4] and [R², U], including all endpoints. To approximate an allowed distribution ρ, round each
squared radius u ≤ U within its own interval, and move every u > U to U. Let P denote the operation
on radial distributions defined by this rounding and truncation procedure. The resulting
distribution Pρ has exactly the same near mass as ρ and satisfies sup_{θ∈I} |Φ_ρ(θ) − Φ_{Pρ}(θ)| ≤ ξ."
and "Write M = |U|. The mesh gives M ≤ C(1 + q(R²/4 + U − R²)/ξ)".

**Formalization Note.**
* Abstract in the parameters: any `0 < θ₀ ≤ q ≤ 1/2` (so `I = [θ₀, q] ⊆ (0, 1/2]`), `R > 0` and
  `ξ > 0` (the paper's `ξ = Γ/1000`); `U` and `s` are as printed, `θ₀^{−2}` is `(θ₀²)⁻¹`.
* Three conclusions: (1) such a grid exists with the size bound, `C` universal; (2) every such grid
  admits a rounding map; (3) for every grid, every rounding map (`IsGrid`, `IsRounding`) and every
  `(R/2, R)`-gapped `ρ`, the grid vector `Pρ` is a probability vector with the same near mass and
  `|Φ_ρ(θ) − Φ_{Pρ}(θ)| ≤ ξ` for all `θ ∈ I`.
* Generalization: (3) holds for every rounding with the stated properties, not one fixed rule.
  `ρ` is a law of radii `r`; the rounding acts on `u = r²`. -/
theorem thm20_grid :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (R θ₀ q ξ : ℝ), 0 < R → 0 < θ₀ → θ₀ ≤ q → q ≤ 1 / 2 → 0 < ξ →
        let U := max (R ^ 2) ((θ₀ ^ 2)⁻¹ * Real.log (8 / ξ))
        let s := ξ / (4 * q)
        (∃ G : Finset ℝ, IsGrid R U s G ∧
          (G.card : ℝ) ≤ C * (1 + q * (R ^ 2 / 4 + U - R ^ 2) / ξ)) ∧
        (∀ G : Finset ℝ, IsGrid R U s G → ∃ round : ℝ → ℝ, IsRounding R U s G round) ∧
        ∀ (G : Finset ℝ) (round : ℝ → ℝ), IsGrid R U s G → IsRounding R U s G round →
          ∀ ρ : Measure ℝ, IsProbabilityMeasure ρ → IsGapped R ρ →
            IsProbVec G (roundedVec ρ round) ∧
            nearMassVec R G (roundedVec ρ round) = nearMass R ρ ∧
            ∀ θ ∈ Set.Icc θ₀ q, ‖PhiRad n ρ θ - PhiVec n G (roundedVec ρ round) θ‖ ≤ ξ := by sorry

end GaussMixHH
