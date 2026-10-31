-- Prove2me | Theorems.Thm_FrechetPrefs_equation_7
-- name    : FrechetPrefs.equation_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:07.238995+00:00
-- url     : https://prove2.me/theorems/6d8a62de-2583-4c9e-9760-5a7ba8281826
-- title:
--   Equation (7), p.11 — the two value formulas (corrected: minimum over the floor class)
-- statement:
--   Under Assumptions 1 and 2, let $0<K<K_B$, $Q_B$ the barycenter, $\theta>\theta_c$, and let $Q$ be a measure of the floor class whose quantile $F_\theta^{-1}$ solves (5) on $(0,1)$. Then
--   $$U_\theta(X)=\int_0^1u(F_\theta^{-1}(s))\,ds+\frac\theta2\int_0^1\big(F_\theta^{-1}(s)-F_B^{-1}(s)\big)^2ds=\int_0^1u(F_\theta^{-1}(s))\,ds+\frac1{2\theta}\int_0^1\big(u'(F_\theta^{-1}(s))\big)^2ds.$$
--
--   The first form substitutes the minimizer into the objective and the second uses (5).
--
--   Differences from the source:
--   - correction: "A minimizer Q_θ of problem (4) in P(R)" → the minimum is over the floor class {μ ∈ P₂ : μ((−∞,K)) = 0}; reason: the printed claim is false: for u = log, n = 1, Q₁ = δ₂, K₁ = 1 the objective at ½δ₂ + ½δ_t tends to −∞ as t ↓ 0 for every θ; p.11 and p.ec5 make this restriction themselves
--   - encoding: Assumption 2: Q_j(X ∈ [0,K_j]) = 0 with X positive → Q_j((−∞,K_j]) = 0 and K_j > 0; reason: the positivity of X is stated on pp.10–11, so the two sets carry the same mass
--   - encoding: models in P(ℝ) → models in P₂(ℝ); reason: the distance of eq. (1) is an L² norm of quantiles: the paper takes Q ⊂ L²([0,1]), p.26, and writes P₂(ℝ) on p.ec6
--   - encoding: quantile functions on [0,1] → quantiles evaluated on the open interval (0,1); reason: the endpoints are null, and F⁻¹(1) can be infinite; no integral changes
--   - generalization: the floor K* = minᵢ Kᵢ, with θ_c dividing by K_B − K* → any floor K with 0 < K < K_B, with threshold max{|u″(K)|, u′(K)/(K_B − K)}; reason: it specializes to K = K* whenever K* < K_B, and it also covers K* = K_B (for example n = 1), where (EC.11) divides by zero
--   - generalization: continuous quantiles "for simplicity" (p.ec5) → all measures of P₂, with left-continuous quantiles; reason: continuous quantiles are a special case
-- source:
--   Petracou, Xepapadeas, Yannacopoulos, Decision Making under Model Uncertainty: Fréchet-Wasserstein Mean Preferences, manuscript MS-DEC-19-01009-REV (accepted manuscript, hdl.handle.net/11585/863779), eq. (7), p.11; Appendix B, p.27; p.ec6

import Mathlib
import Definitions.Def_FrechetPrefs_InadaUtility
import Definitions.Def_FrechetPrefs_Multiplier

open MeasureTheory Set Filter Topology

namespace FrechetPrefs

/-- Equation (7), p.11, with Appendix B, p.27 and p.ec6 of manuscript MS-DEC-19-01009-REV: for a
measure of the floor class whose quantile `g` solves (5) on `(0,1)`,
`U_θ(X) = ∫₀¹ u(g) ds + (θ/2) ∫₀¹ (g − F_B⁻¹)² ds = ∫₀¹ u(g) ds + (1/2θ) ∫₀¹ (u′(g))² ds`. -/
theorem equation_7 {n : ℕ} (w : Fin n → ℝ) (Q : Fin n → ProbabilityMeasure ℝ) (Kv : Fin n → ℝ)
    (u : ℝ → ℝ) (B : ProbabilityMeasure ℝ) (K : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hQ : ∀ i, Q i ∈ P2)
    (hAss2 : ∀ i, 0 < Kv i ∧ (Q i : Measure ℝ) (Iic (Kv i)) = 0)
    (hu : IsInadaUtility u) (hB : IsBarycenter w Q B)
    (hK0 : 0 < K) (hK : K < KB w Kv) (θ : ℝ)
    (hθ : thetaC u K (KB w Kv) < θ) (μ : ProbabilityMeasure ℝ) (hμ : μ ∈ floorClass K)
    (hsol : ∀ s ∈ Ioo (0 : ℝ) 1, 1 / θ * deriv u (q μ s) + q μ s = q B s) :
    multiplierUtility u w Q B θ K =
        ∫ s in Ioo (0 : ℝ) 1, u (q μ s) + θ / 2 * ∫ s in Ioo (0 : ℝ) 1, (q μ s - q B s) ^ 2 ∧
    multiplierUtility u w Q B θ K =
        ∫ s in Ioo (0 : ℝ) 1, u (q μ s) +
          1 / (2 * θ) * ∫ s in Ioo (0 : ℝ) 1, (deriv u (q μ s)) ^ 2 := by sorry

end FrechetPrefs
