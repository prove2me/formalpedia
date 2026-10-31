-- Prove2me | Theorems.Thm_FrechetPrefs_limits
-- name    : FrechetPrefs.limits
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:56.418751+00:00
-- url     : https://prove2.me/theorems/9883f506-fe98-4e79-9c34-d76c3e6eb1e2
-- title:
--   Appendix B, p.27 — $F_\theta^{-1}\to F_B^{-1}$ and $U_\theta\to U_B$ as $\theta\to\infty$ (corrected: minimum over the floor class)
-- statement:
--   Under Assumptions 1 and 2, let $0<K<K_B$, $Q_B$ the barycenter, and for every $\theta>\theta_c$ let $Q_\theta$ be a measure of the floor class whose quantile $F_\theta^{-1}$ solves (5) on $(0,1)$. Then for $\theta>\theta_c$ and $s\in(0,1)$,
--   $$0\le F_B^{-1}(s)-F_\theta^{-1}(s)\le\frac{u'(K)}\theta,$$
--   hence $F_\theta^{-1}\to F_B^{-1}$ uniformly on $(0,1)$ as $\theta\to\infty$, and
--   $$U_\theta(X)\to\mathbb E_{Q_B}[u(X)].$$
--
--   As uncertainty aversion vanishes, the multiplier preferences reduce to the barycentric expected utility.
--
--   Differences from the source:
--   - correction: "A minimizer Q_θ of problem (4) in P(R)" → the minimum is over the floor class {μ ∈ P₂ : μ((−∞,K)) = 0}; reason: the printed claim is false: for u = log, n = 1, Q₁ = δ₂, K₁ = 1 the objective at ½δ₂ + ½δ_t tends to −∞ as t ↓ 0 for every θ; p.11 and p.ec5 make this restriction themselves
--   - generalization: F_θ⁻¹ → F_B⁻¹ as θ → ∞, pointwise → uniform convergence on (0,1), with the rate u′(K)/θ; reason: uniform convergence implies the printed limit
--   - encoding: Assumption 2: Q_j(X ∈ [0,K_j]) = 0 with X positive → Q_j((−∞,K_j]) = 0 and K_j > 0; reason: the positivity of X is stated on pp.10–11, so the two sets carry the same mass
--   - encoding: models in P(ℝ) → models in P₂(ℝ); reason: the distance of eq. (1) is an L² norm of quantiles: the paper takes Q ⊂ L²([0,1]), p.26, and writes P₂(ℝ) on p.ec6
--   - encoding: quantile functions on [0,1] → quantiles evaluated on the open interval (0,1); reason: the endpoints are null, and F⁻¹(1) can be infinite; no integral changes
--   - generalization: the floor K* = minᵢ Kᵢ, with θ_c dividing by K_B − K* → any floor K with 0 < K < K_B, with threshold max{|u″(K)|, u′(K)/(K_B − K)}; reason: it specializes to K = K* whenever K* < K_B, and it also covers K* = K_B (for example n = 1), where (EC.11) divides by zero
--   - generalization: continuous quantiles "for simplicity" (p.ec5) → all measures of P₂, with left-continuous quantiles; reason: continuous quantiles are a special case
-- source:
--   Petracou, Xepapadeas, Yannacopoulos, Decision Making under Model Uncertainty: Fréchet-Wasserstein Mean Preferences, manuscript MS-DEC-19-01009-REV (accepted manuscript, hdl.handle.net/11585/863779), Appendix B, p.27

import Mathlib
import Definitions.Def_FrechetPrefs_InadaUtility
import Definitions.Def_FrechetPrefs_Multiplier

open MeasureTheory Set Filter Topology

namespace FrechetPrefs

/-- Appendix B, p.27 of manuscript MS-DEC-19-01009-REV: `F_θ⁻¹ → F_B⁻¹` and `U_θ(X) → E_{Q_B}[u(X)]` as
`θ → ∞`, for any family of floor-class measures whose quantiles solve (5). The explicit bound
`0 ≤ F_B⁻¹ − F_θ⁻¹ ≤ u′(K)/θ` makes the first limit uniform on `(0,1)`. -/
theorem limits {n : ℕ} (w : Fin n → ℝ) (Q : Fin n → ProbabilityMeasure ℝ) (Kv : Fin n → ℝ)
    (u : ℝ → ℝ) (B : ProbabilityMeasure ℝ) (K : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hQ : ∀ i, Q i ∈ P2)
    (hAss2 : ∀ i, 0 < Kv i ∧ (Q i : Measure ℝ) (Iic (Kv i)) = 0)
    (hu : IsInadaUtility u) (hB : IsBarycenter w Q B)
    (hK0 : 0 < K) (hK : K < KB w Kv) (Qθ : ℝ → ProbabilityMeasure ℝ)
    (hfam : ∀ θ, thetaC u K (KB w Kv) < θ → Qθ θ ∈ floorClass K ∧
      ∀ s ∈ Ioo (0 : ℝ) 1, 1 / θ * deriv u (q (Qθ θ) s) + q (Qθ θ) s = q B s) :
    (∀ θ, thetaC u K (KB w Kv) < θ → ∀ s ∈ Ioo (0 : ℝ) 1,
      0 ≤ q B s - q (Qθ θ) s ∧ q B s - q (Qθ θ) s ≤ deriv u K / θ) ∧
    TendstoUniformlyOn (fun θ s => q (Qθ θ) s) (q B) atTop (Ioo 0 1) ∧
    Tendsto (fun θ => multiplierUtility u w Q B θ K) atTop
      (𝓝 (∫ x, u x ∂(B : Measure ℝ))) := by sorry

end FrechetPrefs
