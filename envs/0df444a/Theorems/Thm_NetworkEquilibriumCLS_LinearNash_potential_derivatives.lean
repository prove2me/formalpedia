-- Prove2me | Theorems.Thm_NetworkEquilibriumCLS_LinearNash_potential_derivatives
-- name    : NetworkEquilibriumCLS.LinearNash.potential_derivatives
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:29.436591+00:00
-- url     : https://prove2.me/theorems/05b44199-4220-4136-a422-066e38f58b18
-- title:
--   Lemma 4.1 — all four derivatives of the constructed potential
-- statement:
--   Let p have a symmetric rational Q with |Q_{ii}|≤1, and let h be an integer square-free quadratic in a positive number of variables. Use the full Section 4 potential Φ, controls s,s′, averages z and s̄, disagreements d, τ, and residual R defined by Eqs. (3)–(7). For every real cube point and every q,i,
--
--   $$\partial_{x_{q,i}}\Phi=\frac{\tau^2}4\left[F_i(z_q)+(1-Q_{ii}/2)d_{q,i}\right]-\tau R_q,$$
--   $$\partial_{y_{q,i}}\Phi=\frac{\tau^2}4\left[F_i(z_q)-(1-Q_{ii}/2)d_{q,i}\right]+\tau R_q,$$
--   $$\partial_{s_q}\Phi=R_q/2+(s_q-s'_q)/16,\qquad\partial_{s'_q}\Phi=R_q/2-(s_q-s'_q)/16.$$
--
--   All four equalities concern the actual coordinate derivatives of the explicitly evaluated polynomial. These identities expose the common residual used by both decoding cases.
--
--   Differences from the source:
--   - encoding: positive dimensions and indices 1 through d → Fin d with d positive and indices 0 through d-1; reason: a bijective relabelling; all real-cube coordinates and all boundary cases are retained
--   - generalization: h obtained from the Boolean local-search reduction for p → any integer square-free quadratic h of positive dimension; reason: the analytic proof uses only integer coefficients, the row-sum bound, and the stated polynomial; taking the h supplied by Lemma 3.2 recovers the source
-- source:
--   Ioannis Anagnostides, Ioannis Panageas, Jingming Yan, STOC 2027 submission #653 (October 2026), p.11 (PDF 12), Lemma 4.1.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Potential

namespace NetworkEquilibriumCLS.LinearNash

/-- Source and every encoding convention are recorded in the item metadata. -/
theorem potential_derivatives :
    ∀ (m n : ℕ), 0 < m → 0 < n →
    ∀ (p : Quadratic m) (h : BooleanPolynomial n) (v : Coordinate m n → ℝ),
      IsNormalized p → InCube v → ∀ (q : Fin n) (i : Fin m),
      coordinatePartial (potential p h) v (xIndex q i) =
        (tau m h)^2 / 4 * (sourceGradient p (averageZ v q) i +
          (1 - (p.Q i i : ℝ)/2) * differenceD v q i) - tau m h * residual h v q ∧
      coordinatePartial (potential p h) v (yIndex q i) =
        (tau m h)^2 / 4 * (sourceGradient p (averageZ v q) i -
          (1 - (p.Q i i : ℝ)/2) * differenceD v q i) + tau m h * residual h v q ∧
      coordinatePartial (potential p h) v (sIndex q) =
        residual h v q / 2 + (controlS v q - controlT v q)/16 ∧
      coordinatePartial (potential p h) v (tIndex q) =
        residual h v q / 2 - (controlS v q - controlT v q)/16 := by sorry

end NetworkEquilibriumCLS.LinearNash
