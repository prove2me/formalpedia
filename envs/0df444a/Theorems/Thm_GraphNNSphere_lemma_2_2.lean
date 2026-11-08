-- Prove2me | Theorems.Thm_GraphNNSphere_lemma_2_2
-- name    : GraphNNSphere.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:41:36.209796+00:00
-- url     : https://prove2.me/theorems/a50899d7-a794-47df-adfe-97cf6c8c48a9
-- title:
--   Lemma 2.2 — the lens rate
-- statement:
--   Let $\delta(x,q)=\theta\in(0,\pi/2)$ and $0<\rho<\pi/2$, and let $J_\theta(\rho)$ be the lens rate. For every fixed $\varepsilon>0$:
--
--   1. Uniformly for $0<\theta\le\pi/2-\varepsilon$ and $0<\rho\le\pi/2-\varepsilon$,
--   $$\frac{\sigma_{d-1}(C(x,\rho)\cap C(q,\theta))}{F(\theta)}=\exp\bigl\{-(d-1)J_\theta(\rho)+O\bigl(\log(d-1)+\log(1/\sin\theta)+\log(1/\sin\rho)\bigr)\bigr\}.$$
--   If $\rho\ge\varepsilon\theta$, the error simplifies to $O(\log(d-1)+\log(1/\sin\theta))$.
--   2. Uniformly for $0<\theta\le\pi/2-\varepsilon$ and $0<\rho<\pi/2$,
--   $$\frac{\sigma_{d-1}(C(x,\rho)\cap C(q,\theta))}{F(\theta)}\le e^{-(d-1)J_\theta(\rho)}\bigl(1+O(d^{-1})\bigr).$$
--
--   The ratio on the left is the fraction of improving locations available within the neighbor radius $\rho$.
--
--   Differences from the source:
--   - encoding: exp{−(d−1)J + O(E)} and 1 + O(d⁻¹) → |log(ratio) + (d−1)J| ≤ C·E and 1 + C/d, for d ≥ D₀, with C, D₀ depending only on ε; reason: the standard meaning of the asymptotic notation at this quantifier position (§2.1)
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Lemma 2.2, p.15

import Mathlib
import Definitions.Def_GraphNNSphere_capMass
import Definitions.Def_GraphNNSphere_Jrate

namespace GraphNNSphere

/-- Lemma 2.2, the lens rate (Lu, *Sharp Limits of Graph-Based Nearest
Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Lemma 2.2, p.15).

**Formalization Note** `exp{-(d-1)J + O(E)}` is `|log(ratio) + (d-1)J| ≤ C·E`, and `1 + O(d⁻¹)` is
`1 + C/d`, for `d ≥ D₀`. The constants `C`, `D₀` depend only on `ε`, and are uniform in `x`, `q`,
`θ`, `ρ`. -/
theorem lemma_2_2 (ε : ℝ) (hε : 0 < ε) :
    (∃ C : ℝ, ∃ D₀ : ℕ, ∀ d : ℕ, D₀ ≤ d → ∀ (x q : Sph d) (θ ρ : ℝ), geo x q = θ → 0 < θ →
      θ ≤ Real.pi / 2 - ε → 0 < ρ → ρ ≤ Real.pi / 2 - ε →
      |Real.log ((unif d (cap x ρ ∩ cap q θ)).toReal / capMass d θ) +
          ((d : ℝ) - 1) * Jrate θ ρ| ≤
        C * (Real.log ((d : ℝ) - 1) + Real.log (1 / Real.sin θ) + Real.log (1 / Real.sin ρ)) ∧
      (ε * θ ≤ ρ →
        |Real.log ((unif d (cap x ρ ∩ cap q θ)).toReal / capMass d θ) +
            ((d : ℝ) - 1) * Jrate θ ρ| ≤
          C * (Real.log ((d : ℝ) - 1) + Real.log (1 / Real.sin θ)))) ∧
    (∃ C : ℝ, ∃ D₀ : ℕ, ∀ d : ℕ, D₀ ≤ d → ∀ (x q : Sph d) (θ ρ : ℝ), geo x q = θ → 0 < θ →
      θ ≤ Real.pi / 2 - ε → 0 < ρ → ρ < Real.pi / 2 →
      (unif d (cap x ρ ∩ cap q θ)).toReal / capMass d θ ≤
        Real.exp (-(((d : ℝ) - 1) * Jrate θ ρ)) * (1 + C / (d : ℝ))) := by sorry

end GraphNNSphere
