-- Prove2me | Theorems.Thm_FrechetPrefs_utility_expansion
-- name    : FrechetPrefs.utility_expansion
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:15.827102+00:00
-- url     : https://prove2.me/theorems/8b771524-9a9c-4a40-a39b-7e217aaba1d7
-- title:
--   (8), p.11 and p.ec7 — expansion of $U_\theta$ (corrected: needs $u'''$ bounded)
-- statement:
--   Under Assumptions 1 and 2, let $u\in C^3$ with $u^{(3)}$ bounded on $[K,\sup_sF_B^{-1}(s))$, $0<K<K_B$, and $Q_B$ the barycenter. There are $C$ and $\Theta$ such that for all $\theta\ge\Theta$,
--   $$\Big|U_\theta(X)-\mathbb E_{Q_B}\Big[u(X)-\frac{(u'(X))^2}{2\theta}+\frac{(u'(X))^2u''(X)}{2\theta^2}\Big]\Big|\le\frac C{\theta^3}.$$
--
--   This is the expected-utility form of the multiplier preferences up to second order: it is the link between uncertainty aversion and risk aversion.
--
--   Differences from the source:
--   - correction: O(1/θ³) in (8) read uniformly in s (Remark EC.3) and integrated into U_θ, with u ∈ C³ only → the uniform bound and the bound on U_θ assume u‴ bounded on [K, sup F_B⁻¹); reason: with u ∈ C³ only they fail for unbounded support: a u with u″ = −b, b piecewise constant with narrow steps at the integers, and Q₁ = Σ 2^{−k} δ_{k+1}; condition (EC.13) names this dependence, and the bound is automatic for bounded F_B⁻¹
--   - correction: "A minimizer Q_θ of problem (4) in P(R)" → the minimum is over the floor class {μ ∈ P₂ : μ((−∞,K)) = 0}; reason: the printed claim is false: for u = log, n = 1, Q₁ = δ₂, K₁ = 1 the objective at ½δ₂ + ½δ_t tends to −∞ as t ↓ 0 for every θ; p.11 and p.ec5 make this restriction themselves
--   - encoding: Assumption 2: Q_j(X ∈ [0,K_j]) = 0 with X positive → Q_j((−∞,K_j]) = 0 and K_j > 0; reason: the positivity of X is stated on pp.10–11, so the two sets carry the same mass
--   - encoding: models in P(ℝ) → models in P₂(ℝ); reason: the distance of eq. (1) is an L² norm of quantiles: the paper takes Q ⊂ L²([0,1]), p.26, and writes P₂(ℝ) on p.ec6
--   - generalization: the floor K* = minᵢ Kᵢ, with θ_c dividing by K_B − K* → any floor K with 0 < K < K_B, with threshold max{|u″(K)|, u′(K)/(K_B − K)}; reason: it specializes to K = K* whenever K* < K_B, and it also covers K* = K_B (for example n = 1), where (EC.11) divides by zero
--   - generalization: continuous quantiles "for simplicity" (p.ec5) → all measures of P₂, with left-continuous quantiles; reason: continuous quantiles are a special case
--   - encoding: V_θ(x) = u(x)(1 − (1/2θ)(u′)²/u + (1/2θ²)(u′)²u″/u) + O(1/θ³) → `effectiveUtility` multiplied out, with the O stated as an explicit bound; reason: the printed form divides by u(x), which can vanish; the two agree where u(x) ≠ 0
--   - encoding: O(1/θ³) "for sufficiently large θ" → ∃ C Θ, ∀ θ ≥ Θ, |…| ≤ C/θ³; reason: the definition of the symbol
-- source:
--   Petracou, Xepapadeas, Yannacopoulos, Decision Making under Model Uncertainty: Fréchet-Wasserstein Mean Preferences, manuscript MS-DEC-19-01009-REV (accepted manuscript, hdl.handle.net/11585/863779), eq. (8), p.11; p.ec7

import Mathlib
import Definitions.Def_FrechetPrefs_InadaUtility
import Definitions.Def_FrechetPrefs_Multiplier

open MeasureTheory Set Filter Topology

namespace FrechetPrefs

/-- The expansion of `U_θ`, (8), p.11 and p.ec7 of manuscript MS-DEC-19-01009-REV:
`U_θ(X) = E_{Q_B}[V_θ(X)]`, with `V_θ = u − (u′)²/(2θ) + (u′)²u″/(2θ²) + O(1/θ³)`, when `u` is `C³` and `u‴` is
bounded on `[K, sup F_B⁻¹)`.

**Formalization Note.** The bound on `u‴` is correction C2 of the mission description. `u‴` is the
iterated `deriv`, the true third derivative on `(0,∞)`. -/
theorem utility_expansion {n : ℕ} (w : Fin n → ℝ) (Q : Fin n → ProbabilityMeasure ℝ) (Kv : Fin n → ℝ)
    (u : ℝ → ℝ) (B : ProbabilityMeasure ℝ) (K : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hQ : ∀ i, Q i ∈ P2)
    (hAss2 : ∀ i, 0 < Kv i ∧ (Q i : Measure ℝ) (Iic (Kv i)) = 0)
    (hu : IsInadaUtility u) (hB : IsBarycenter w Q B)
    (hK0 : 0 < K) (hK : K < KB w Kv) (hu3 : ContDiffOn ℝ 3 u (Ioi 0))
    (hM : ∃ M : ℝ, ∀ x, K ≤ x → (∃ s ∈ Ioo (0 : ℝ) 1, x ≤ q B s) →
      |deriv (deriv (deriv u)) x| ≤ M) :
    ∃ C Θ : ℝ, ∀ θ, Θ ≤ θ →
      |multiplierUtility u w Q B θ K - ∫ x, effectiveUtility u θ x ∂(B : Measure ℝ)| ≤
        C / θ ^ 3 := by sorry

end FrechetPrefs
