-- Prove2me | Theorems.Thm_FrechetPrefs_multiplier_le_barycentric
-- name    : FrechetPrefs.multiplier_le_barycentric
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:06.935258+00:00
-- url     : https://prove2.me/theorems/ab85940c-01d3-469b-943b-9192b406cfb9
-- title:
--   p.ec6 and Appendix B, p.27 — $U_\theta\le U_B$ for all $\theta>0$ (corrected: minimum over the floor class)
-- statement:
--   Under Assumptions 1 and 2, let $0<K<K_B$, $Q_B$ the barycenter and $\theta>0$. Then $Q_B$ belongs to the floor class and
--   $$U_\theta(X)\le\mathbb E_{Q_B}[u(X)]=U_B(X).$$
--
--   This is the pessimism of the multiplier preferences: $Q_B$ is feasible and carries zero penalty.
--
--   Differences from the source:
--   - correction: "A minimizer Q_θ of problem (4) in P(R)" → the minimum is over the floor class {μ ∈ P₂ : μ((−∞,K)) = 0}; reason: the printed claim is false: for u = log, n = 1, Q₁ = δ₂, K₁ = 1 the objective at ½δ₂ + ½δ_t tends to −∞ as t ↓ 0 for every θ; p.11 and p.ec5 make this restriction themselves
--   - encoding: Assumption 2: Q_j(X ∈ [0,K_j]) = 0 with X positive → Q_j((−∞,K_j]) = 0 and K_j > 0; reason: the positivity of X is stated on pp.10–11, so the two sets carry the same mass
--   - encoding: models in P(ℝ) → models in P₂(ℝ); reason: the distance of eq. (1) is an L² norm of quantiles: the paper takes Q ⊂ L²([0,1]), p.26, and writes P₂(ℝ) on p.ec6
--   - generalization: the floor K* = minᵢ Kᵢ, with θ_c dividing by K_B − K* → any floor K with 0 < K < K_B, with threshold max{|u″(K)|, u′(K)/(K_B − K)}; reason: it specializes to K = K* whenever K* < K_B, and it also covers K* = K_B (for example n = 1), where (EC.11) divides by zero
--   - generalization: continuous quantiles "for simplicity" (p.ec5) → all measures of P₂, with left-continuous quantiles; reason: continuous quantiles are a special case
-- source:
--   Petracou, Xepapadeas, Yannacopoulos, Decision Making under Model Uncertainty: Fréchet-Wasserstein Mean Preferences, manuscript MS-DEC-19-01009-REV (accepted manuscript, hdl.handle.net/11585/863779), p.ec6; Appendix B, p.27

import Mathlib
import Definitions.Def_FrechetPrefs_InadaUtility
import Definitions.Def_FrechetPrefs_Multiplier

open MeasureTheory Set Filter Topology

namespace FrechetPrefs

/-- p.ec6 and Appendix B, p.27 of manuscript MS-DEC-19-01009-REV: `U_θ(X) ≤ U_B(X) = E_{Q_B}[u(X)]` for
all `θ > 0`, because `Q_B` is itself feasible and carries zero penalty.

**Formalization Note.** The objective is bounded below on the floor class for every `θ > 0`, so the
real `sInf` of `multiplierUtility` is a genuine infimum here, even below the threshold. -/
theorem multiplier_le_barycentric {n : ℕ} (w : Fin n → ℝ) (Q : Fin n → ProbabilityMeasure ℝ) (Kv : Fin n → ℝ)
    (u : ℝ → ℝ) (B : ProbabilityMeasure ℝ) (K : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hQ : ∀ i, Q i ∈ P2)
    (hAss2 : ∀ i, 0 < Kv i ∧ (Q i : Measure ℝ) (Iic (Kv i)) = 0)
    (hu : IsInadaUtility u) (hB : IsBarycenter w Q B)
    (hK0 : 0 < K) (hK : K < KB w Kv) (θ : ℝ) (hθ : 0 < θ) :
    B ∈ floorClass K ∧ multiplierUtility u w Q B θ K ≤ ∫ x, u x ∂(B : Measure ℝ) := by sorry

end FrechetPrefs
