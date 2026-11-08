-- Prove2me | Theorems.Thm_GraphNNSphere_lemma_2_1
-- name    : GraphNNSphere.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:41:29.281514+00:00
-- url     : https://prove2.me/theorems/04a1863f-b92a-4a40-9810-c5266da4402f
-- title:
--   Lemma 2.1 — spherical cap asymptotics and the angular density
-- statement:
--   Write $F=F_{d-1}$ for the normalized mass of a spherical cap in $S^{d-1}$ and $\alpha_{d-1}=\Gamma(d/2)/(\sqrt\pi\,\Gamma((d-1)/2))$.
--
--   1. For every fixed $\varepsilon>0$, uniformly for $0<\theta\le\pi/2-\varepsilon$,
--   $$F(\theta)=\frac{(\sin\theta)^{d-1}}{\sqrt{2\pi(d-1)}\cos\theta}\bigl(1+O(d^{-1})\bigr).$$
--   2. For $d\ge2$ and $0<\theta<\pi$, the angular density is $F'(\theta)=\alpha_{d-1}(\sin\theta)^{d-2}$.
--   3. The normalizing constant satisfies $\alpha_{d-1}=\sqrt{\tfrac{d-1}{2\pi}}\,\bigl(1+O(d^{-1})\bigr)$.
--   4. For $d\ge 2$ and $0<\theta<\pi/2$ there is a number $\xi$ with $0\le\xi\le\tan^2\theta/(d-1)$ and
--   $$F(\theta)=\frac{\alpha_{d-1}(\sin\theta)^{d-1}}{(d-1)\cos\theta}(1+\xi)^{-1}.$$
--
--   These estimates convert neighbor radii into degree scales for uniform data.
--
--   Differences from the source:
--   - encoding: 1 + O(d⁻¹) → an explicit relative error ≤ C/d for d ≥ D₀, with C, D₀ depending only on ε (and absolute in clause 3); reason: the standard meaning of the asymptotic notation at this quantifier position (§2.1)
--   - reading: no range of d printed for F′ and for the exact remainder → d ≥ 2 and, for F′, 0 < θ < π; reason: the formulas need d ≥ 2 (the denominators d − 1 and the exponent d − 2), and the density is stated on [0, π] in the proof
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Lemma 2.1, p.14

import Mathlib
import Definitions.Def_GraphNNSphere_capMass
import Definitions.Def_GraphNNSphere_alphaNorm

namespace GraphNNSphere

/-- Lemma 2.1, spherical cap asymptotics (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search
on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Lemma 2.1, p.14).

**Formalization Note** `1 + O(d⁻¹)` is an explicit relative error `≤ C / d` for `d ≥ D₀`, with `C`
and `D₀` depending only on `ε`. The derivative and the exact form hold for every `d ≥ 2`. -/
theorem lemma_2_1 :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∃ D₀ : ℕ, ∀ d : ℕ, D₀ ≤ d → ∀ θ : ℝ, 0 < θ → θ ≤ Real.pi / 2 - ε →
      |capMass d θ * (Real.sqrt (2 * Real.pi * ((d : ℝ) - 1)) * Real.cos θ) /
          Real.sin θ ^ (d - 1) - 1| ≤ C / (d : ℝ)) ∧
    (∀ d : ℕ, 2 ≤ d → ∀ θ : ℝ, 0 < θ → θ < Real.pi →
      HasDerivAt (capMass d) (alphaNorm d * Real.sin θ ^ (d - 2)) θ) ∧
    (∃ C : ℝ, ∃ D₀ : ℕ, ∀ d : ℕ, D₀ ≤ d →
      |alphaNorm d / Real.sqrt (((d : ℝ) - 1) / (2 * Real.pi)) - 1| ≤ C / (d : ℝ)) ∧
    (∀ d : ℕ, 2 ≤ d → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      ∃ ξ : ℝ, 0 ≤ ξ ∧ ξ ≤ Real.tan θ ^ 2 / ((d : ℝ) - 1) ∧
        capMass d θ = alphaNorm d * Real.sin θ ^ (d - 1) / (((d : ℝ) - 1) * Real.cos θ) *
          (1 + ξ)⁻¹) := by sorry

end GraphNNSphere
