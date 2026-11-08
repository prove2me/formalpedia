-- Prove2me | Theorems.Thm_GraphNNSphere_boundary_rates
-- name    : GraphNNSphere.boundary_rates
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:38:25.48642+00:00
-- url     : https://prove2.me/theorems/ad133fcb-c225-460f-ac68-f41e184c0e17
-- title:
--   Proof of Theorem 3.1(b) — the rates at the lens boundary and $\beta^*(c)$
-- statement:
--   Fix $\theta\in(0,\pi/2)$. Then
--   $$I_\theta(r^*(\theta))=\tfrac12\log(1+\cos^2\theta)\quad\text{and}\quad J_\theta(r^*(\theta))=0.$$
--   The rate $I_\theta(\rho)$ increases with $\rho$, whereas $J_\theta(\rho)$ decreases to zero as $\rho$ increases to $r^*(\theta)$. Further, $J_\theta(\rho)>0$ for $\rho<r^*(\theta)$ and $J_\theta(\rho)=0$ for $\rho\ge r^*(\theta)$. Both rates are continuous on their parameter ranges. For the limiting angle $\theta_\infty=\arcsin(e^{-1/c})$,
--   $$c\,I_{\theta_\infty}(r^*(\theta_\infty))=\beta^*(c).$$
--
--   This identifies the critical exponent $\beta^*(c)$ as the value of the directional rate at the lens boundary.
--
--   Differences from the source:
--   - reading: "continuous on the parameter ranges used below" → joint continuity of I on {0 < θ < π/2, 0 < ρ < π, cot θ tan(ρ/2) < 1} and of J on (0, π/2)²; reason: the full domains of the rates contain the ranges used; the stronger reading
--   - reading: "I increases with ρ"; "J decreases to zero as ρ increases to r*"; "J = 0 for ρ ≥ r*" → strict monotonicity on the stated domains; the zero clause for r* ≤ ρ < π/2; reason: the domain of J in Lemma 2.2 is 0 < ρ < π/2
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), proof of Theorem 3.1(b), p.25; positivity of J from §2.3, p.16

import Mathlib
import Definitions.Def_GraphNNSphere_Jrate
import Definitions.Def_GraphNNSphere_Irate
import Definitions.Def_GraphNNSphere_rStar
import Definitions.Def_GraphNNSphere_betaStar

namespace GraphNNSphere

/-- The rates at the lens boundary, and the identity for `β*(c)` (Lu, *Sharp Limits of Graph-Based
Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), proof of
Theorem 3.1(b), p.25, with the positivity of `J` from §2.3, p.16).

**Formalization Note** Continuity is joint in `(θ, ρ)`. `J` is the lens rate on `0 < ρ < π/2`, as in
Lemma 2.2. -/
theorem boundary_rates :
    (∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      Irate θ (rStar θ) = 1 / 2 * Real.log (1 + Real.cos θ ^ 2) ∧
      Jrate θ (rStar θ) = 0 ∧
      StrictMonoOn (Irate θ) {ρ | ρ ∈ Set.Ioo 0 Real.pi ∧ Real.cot θ * Real.tan (ρ / 2) < 1} ∧
      StrictAntiOn (Jrate θ) (Set.Ioc 0 (rStar θ)) ∧
      (∀ ρ, 0 < ρ → ρ < rStar θ → 0 < Jrate θ ρ) ∧
      (∀ ρ, rStar θ ≤ ρ → ρ < Real.pi / 2 → Jrate θ ρ = 0)) ∧
    ContinuousOn (fun p : ℝ × ℝ => Irate p.1 p.2)
      {p | 0 < p.1 ∧ p.1 < Real.pi / 2 ∧ 0 < p.2 ∧ p.2 < Real.pi ∧
        Real.cot p.1 * Real.tan (p.2 / 2) < 1} ∧
    ContinuousOn (fun p : ℝ × ℝ => Jrate p.1 p.2)
      {p | 0 < p.1 ∧ p.1 < Real.pi / 2 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2} ∧
    (∀ c : ℝ, 0 < c →
      c * Irate (Real.arcsin (Real.exp (-1 / c))) (rStar (Real.arcsin (Real.exp (-1 / c)))) =
        betaStar c) := by sorry

end GraphNNSphere
