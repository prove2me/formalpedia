-- Prove2me | Theorems.Thm_FrechetPrefs_exists_quantile_solution
-- name    : FrechetPrefs.exists_quantile_solution
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:10.501465+00:00
-- url     : https://prove2.me/theorems/d4b12134-1b34-4d06-b671-c3671c3da782
-- title:
--   (EC.11), p.ec6, and Appendix B, p.27 — the solution of (5) is a quantile function
-- statement:
--   Under Assumptions 1 and 2, let $0<K<K_B$, $Q_B$ the barycenter, and $\theta>\theta_c$. There is a measure $Q$ in the floor class at $K$ whose quantile $g=F^{-1}$ satisfies, for all $s\in(0,1)$,
--   $$\frac1\theta u'(g(s))+g(s)=F_B^{-1}(s),\qquad K<g(s)\le F_B^{-1}(s).$$
--
--   So $g_\theta=\psi^{-1}\circ F_B^{-1}$ is an admissible quantile: this is where equation (5) stops being a formal first-order condition.
--
--   Differences from the source:
--   - encoding: Assumption 2: Q_j(X ∈ [0,K_j]) = 0 with X positive → Q_j((−∞,K_j]) = 0 and K_j > 0; reason: the positivity of X is stated on pp.10–11, so the two sets carry the same mass
--   - encoding: models in P(ℝ) → models in P₂(ℝ); reason: the distance of eq. (1) is an L² norm of quantiles: the paper takes Q ⊂ L²([0,1]), p.26, and writes P₂(ℝ) on p.ec6
--   - encoding: quantile functions on [0,1] → quantiles evaluated on the open interval (0,1); reason: the endpoints are null, and F⁻¹(1) can be infinite; no integral changes
--   - generalization: the floor K* = minᵢ Kᵢ, with θ_c dividing by K_B − K* → any floor K with 0 < K < K_B, with threshold max{|u″(K)|, u′(K)/(K_B − K)}; reason: it specializes to K = K* whenever K* < K_B, and it also covers K* = K_B (for example n = 1), where (EC.11) divides by zero
--   - generalization: continuous quantiles "for simplicity" (p.ec5) → all measures of P₂, with left-continuous quantiles; reason: continuous quantiles are a special case
-- source:
--   Petracou, Xepapadeas, Yannacopoulos, Decision Making under Model Uncertainty: Fréchet-Wasserstein Mean Preferences, manuscript MS-DEC-19-01009-REV (accepted manuscript, hdl.handle.net/11585/863779), (EC.11), p.ec6, and Appendix B, p.27

import Mathlib
import Definitions.Def_FrechetPrefs_InadaUtility
import Definitions.Def_FrechetPrefs_Multiplier

open MeasureTheory Set Filter Topology

namespace FrechetPrefs

/-- (EC.11), p.ec6, and Appendix B, p.27 of manuscript MS-DEC-19-01009-REV: for `θ` above the
threshold, the solution `g_θ` of (5) at `ρ = θ` is a quantile function. That is, there is a measure
of the floor class whose quantile solves (5) on `(0,1)` and lies in `(K, F_B⁻¹]`. -/
theorem exists_quantile_solution {n : ℕ} (w : Fin n → ℝ) (Q : Fin n → ProbabilityMeasure ℝ) (Kv : Fin n → ℝ)
    (u : ℝ → ℝ) (B : ProbabilityMeasure ℝ) (K : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hQ : ∀ i, Q i ∈ P2)
    (hAss2 : ∀ i, 0 < Kv i ∧ (Q i : Measure ℝ) (Iic (Kv i)) = 0)
    (hu : IsInadaUtility u) (hB : IsBarycenter w Q B)
    (hK0 : 0 < K) (hK : K < KB w Kv) (θ : ℝ)
    (hθ : thetaC u K (KB w Kv) < θ) :
    ∃ μ : ProbabilityMeasure ℝ, μ ∈ floorClass K ∧
      ∀ s ∈ Ioo (0 : ℝ) 1, 1 / θ * deriv u (q μ s) + q μ s = q B s ∧
        K < q μ s ∧ q μ s ≤ q B s := by sorry

end FrechetPrefs
