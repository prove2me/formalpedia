-- Prove2me | Theorems.Thm_FrechetPrefs_quantile_expansion
-- name    : FrechetPrefs.quantile_expansion
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:44.022381+00:00
-- url     : https://prove2.me/theorems/28db40d9-41c1-4ad7-a5ad-750edb0831a1
-- title:
--   (8), p.11, p.ec7 and Remark EC.3 — expansion of $F_\theta^{-1}$ (corrected: the uniform $O$ needs $u'''$ bounded)
-- statement:
--   Under Assumptions 1 and 2, let $u\in C^3$, $0<K<K_B$, $Q_B$ the barycenter, and for every $\theta>\theta_c$ let $Q_\theta$ be a measure of the floor class whose quantile $F_\theta^{-1}$ solves (5) on $(0,1)$. Write $z=F_B^{-1}(s)$.
--
--   1. For each $s\in(0,1)$ there are $C$ and $\Theta$ such that for all $\theta\ge\Theta$,
--   $$\Big|F_\theta^{-1}(s)-\Big(z-\frac1\theta u'(z)+\frac1{\theta^2}u''(z)u'(z)\Big)\Big|\le\frac C{\theta^3}.$$
--   2. If moreover $u^{(3)}$ is bounded on $[K,\sup_sF_B^{-1}(s))$, then $C$ and $\Theta$ can be chosen independent of $s$.
--
--   The term $-\frac1\theta u'$ is the first-order distortion of the barycenter quantile, and the next term is its curvature correction.
--
--   Differences from the source:
--   - correction: O(1/θ³) in (8) read uniformly in s (Remark EC.3) and integrated into U_θ, with u ∈ C³ only → the uniform bound and the bound on U_θ assume u‴ bounded on [K, sup F_B⁻¹); reason: with u ∈ C³ only they fail for unbounded support: a u with u″ = −b, b piecewise constant with narrow steps at the integers, and Q₁ = Σ 2^{−k} δ_{k+1}; condition (EC.13) names this dependence, and the bound is automatic for bounded F_B⁻¹
--   - correction: "A minimizer Q_θ of problem (4) in P(R)" → the minimum is over the floor class {μ ∈ P₂ : μ((−∞,K)) = 0}; reason: the printed claim is false: for u = log, n = 1, Q₁ = δ₂, K₁ = 1 the objective at ½δ₂ + ½δ_t tends to −∞ as t ↓ 0 for every θ; p.11 and p.ec5 make this restriction themselves
--   - encoding: Assumption 2: Q_j(X ∈ [0,K_j]) = 0 with X positive → Q_j((−∞,K_j]) = 0 and K_j > 0; reason: the positivity of X is stated on pp.10–11, so the two sets carry the same mass
--   - encoding: models in P(ℝ) → models in P₂(ℝ); reason: the distance of eq. (1) is an L² norm of quantiles: the paper takes Q ⊂ L²([0,1]), p.26, and writes P₂(ℝ) on p.ec6
--   - encoding: quantile functions on [0,1] → quantiles evaluated on the open interval (0,1); reason: the endpoints are null, and F⁻¹(1) can be infinite; no integral changes
--   - generalization: the floor K* = minᵢ Kᵢ, with θ_c dividing by K_B − K* → any floor K with 0 < K < K_B, with threshold max{|u″(K)|, u′(K)/(K_B − K)}; reason: it specializes to K = K* whenever K* < K_B, and it also covers K* = K_B (for example n = 1), where (EC.11) divides by zero
--   - generalization: continuous quantiles "for simplicity" (p.ec5) → all measures of P₂, with left-continuous quantiles; reason: continuous quantiles are a special case
--   - encoding: O(1/θ³) "for sufficiently large θ" → ∃ C Θ, ∀ θ ≥ Θ, |…| ≤ C/θ³; reason: the definition of the symbol
-- source:
--   Petracou, Xepapadeas, Yannacopoulos, Decision Making under Model Uncertainty: Fréchet-Wasserstein Mean Preferences, manuscript MS-DEC-19-01009-REV (accepted manuscript, hdl.handle.net/11585/863779), eq. (8), p.11; p.ec7; Remark EC.3, pp.ec7–ec8

import Mathlib
import Definitions.Def_FrechetPrefs_InadaUtility
import Definitions.Def_FrechetPrefs_Multiplier

open MeasureTheory Set Filter Topology

namespace FrechetPrefs

/-- The expansion of `g_θ`, (8), p.11, p.ec7 and Remark EC.3, pp.ec7–ec8 of manuscript
MS-DEC-19-01009-REV: `F_θ⁻¹ = F_B⁻¹ − (1/θ) u′(F_B⁻¹) + (1/θ²) u″(F_B⁻¹) u′(F_B⁻¹) + O(1/θ³)`. The bound
holds for each fixed `s` when `u` is `C³`, and uniformly in `s` when `u‴` is bounded on `[K, sup F_B⁻¹)`,
which is condition (EC.13) of Remark EC.3 in this form.

**Formalization Note.** `T2` is the second-order approximation. The bound on `u‴` restricts the second
clause only, by correction C2 of the mission description. -/
theorem quantile_expansion {n : ℕ} (w : Fin n → ℝ) (Q : Fin n → ProbabilityMeasure ℝ) (Kv : Fin n → ℝ)
    (u : ℝ → ℝ) (B : ProbabilityMeasure ℝ) (K : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hQ : ∀ i, Q i ∈ P2)
    (hAss2 : ∀ i, 0 < Kv i ∧ (Q i : Measure ℝ) (Iic (Kv i)) = 0)
    (hu : IsInadaUtility u) (hB : IsBarycenter w Q B)
    (hK0 : 0 < K) (hK : K < KB w Kv) (hu3 : ContDiffOn ℝ 3 u (Ioi 0))
    (Qθ : ℝ → ProbabilityMeasure ℝ)
    (hfam : ∀ θ, thetaC u K (KB w Kv) < θ → Qθ θ ∈ floorClass K ∧
      ∀ s ∈ Ioo (0 : ℝ) 1, 1 / θ * deriv u (q (Qθ θ) s) + q (Qθ θ) s = q B s) :
    (∀ s ∈ Ioo (0 : ℝ) 1, ∃ C Θ : ℝ, ∀ θ, Θ ≤ θ →
      |q (Qθ θ) s - T2 u θ (q B s)| ≤ C / θ ^ 3) ∧
    ((∃ M : ℝ, ∀ x, K ≤ x → (∃ s ∈ Ioo (0 : ℝ) 1, x ≤ q B s) →
        |deriv (deriv (deriv u)) x| ≤ M) →
      ∃ C Θ : ℝ, ∀ s ∈ Ioo (0 : ℝ) 1, ∀ θ, Θ ≤ θ →
        |q (Qθ θ) s - T2 u θ (q B s)| ≤ C / θ ^ 3) := by sorry

end FrechetPrefs
