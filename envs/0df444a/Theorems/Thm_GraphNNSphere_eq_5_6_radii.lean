-- Prove2me | Theorems.Thm_GraphNNSphere_eq_5_6_radii
-- name    : GraphNNSphere.eq_5_6_radii
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:43:51.785837+00:00
-- url     : https://prove2.me/theorems/378181ae-4f8e-4b49-90ed-a96b8813a8da
-- title:
--   Eqs. (5)–(6) — comparison of cap radii with $\theta_1$
-- statement:
--   Let $d$ be in the logarithmic regime $d=\lfloor c\log n\rfloor$ or in the dense regime. For every fixed $\varepsilon>0$, uniformly for $0<\theta\le\pi/2-\varepsilon$,
--   $$nF(\theta)=\Bigl(\frac{\sin\theta}{\sin\theta_1}\Bigr)^{d-1}\frac{\cos\theta_1}{\cos\theta}\bigl(1+O(d^{-1})\bigr).\tag{5}$$
--   Fix $0<\beta<1$ and $\gamma>0$, with $\gamma<1/c$ in the logarithmic regime, and define $\rho_\beta$, $r_\gamma$ by $nF(\rho_\beta)=n^\beta$ and $nF(r_\gamma)=e^{\gamma d}$. Both radii stay bounded away from $\pi/2$, and
--   $$\frac{\sin\rho_\beta}{\sin\theta_1}=n^{\beta/(d-1)}\bigl(1+O(d^{-1})\bigr),\qquad\frac{\sin r_\gamma}{\sin\theta_1}=e^{\gamma}\bigl(1+O(d^{-1})\bigr).\tag{6}$$
--
--   These express the two degree choices as neighbor radii.
--
--   Differences from the source:
--   - encoding: 1 + O(d⁻¹) and "bounded away from π/2" → an explicit relative error ≤ C/d and an explicit margin ε, for large n; reason: the standard meaning of the asymptotic notation at this quantifier position (§2.1)
--   - encoding: "in both regimes" → one hypothesis d = ⌊c log n⌋ or dense regime, with c a parameter of the first alternative only; reason: same two cases
--   - reading: constants unspecified → C (and the margin) before the sequence d; only the threshold depends on d; reason: the convention of §2.1, the stronger reading, which the estimate gives
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §2.2, Eqs. (5) and (6), p.15

import Mathlib
import Definitions.Def_GraphNNSphere_theta1
import Definitions.Def_GraphNNSphere_rhoBeta
import Definitions.Def_GraphNNSphere_rGamma
import Definitions.Def_GraphNNSphere_logDim
import Definitions.Def_GraphNNSphere_IsDenseRegime

open Filter

namespace GraphNNSphere

/-- Eqs. (5) and (6), comparison of cap radii with `θ₁` (Lu, *Sharp Limits of Graph-Based Nearest
Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §2.2, Eqs. (5)
and (6), p.15).

**Formalization Note** Both regimes are covered by one hypothesis on `d`: either `d = ⌊c log n⌋`
or the dense regime. `c` is a parameter of the logarithmic regime only, and `1 + O(d⁻¹)` is an
explicit relative error `≤ C / d` for large `n`. -/
theorem eq_5_6_radii :
    (∀ c ε : ℝ, 0 < c → 0 < ε → ∃ C : ℝ, ∀ d : ℕ → ℕ, (d = logDim c ∨ IsDenseRegime d) →
      ∀ᶠ n : ℕ in atTop, ∀ θ : ℝ, 0 < θ → θ ≤ Real.pi / 2 - ε →
        |(n : ℝ) * capMass (d n) θ /
            ((Real.sin θ / Real.sin (theta1 n (d n))) ^ (d n - 1) *
              (Real.cos (theta1 n (d n)) / Real.cos θ)) - 1| ≤ C / (d n : ℝ)) ∧
    (∀ c β γ : ℝ, 0 < c → 0 < β → β < 1 → 0 < γ → ∃ ε C : ℝ, 0 < ε ∧
      ∀ d : ℕ → ℕ, ((d = logDim c ∧ γ < 1 / c) ∨ IsDenseRegime d) → ∀ᶠ n : ℕ in atTop,
        rhoBeta n (d n) β ≤ Real.pi / 2 - ε ∧
        rGamma n (d n) γ ≤ Real.pi / 2 - ε ∧
        |(Real.sin (rhoBeta n (d n) β) / Real.sin (theta1 n (d n))) /
            (n : ℝ) ^ (β / ((d n : ℝ) - 1)) - 1| ≤ C / (d n : ℝ) ∧
        |(Real.sin (rGamma n (d n) γ) / Real.sin (theta1 n (d n))) / Real.exp γ - 1| ≤
          C / (d n : ℝ)) := by sorry

end GraphNNSphere
