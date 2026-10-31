-- Prove2me | Theorems.Thm_FrechetPrefs_minimality
-- name    : FrechetPrefs.minimality
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:01.157283+00:00
-- url     : https://prove2.me/theorems/201abfdf-9b28-4d94-a13d-7eb47292f7b2
-- title:
--   Remark EC.1, pp.ec3–ec4 — the solution of (5) is the global minimizer on the floor class (corrected: floor class, not $P(\mathbb R)$)
-- statement:
--   Under Assumptions 1 and 2, let $0<K<K_B$, $Q_B$ the barycenter and $\theta>\theta_c$. Then:
--
--   1. for each real $z$, the function $x\mapsto u(x)+\frac\theta2(x-z)^2$ is strictly convex on $[K,\infty)$;
--   2. if $x\ge K$ and $\psi(x)=z$, this function attains its minimum over $[K,\infty)$ at $x$;
--   3. a measure $Q$ of the floor class whose quantile solves (5) on $(0,1)$ minimizes the objective of (4) over the floor class.
--
--   The remark checks a first-order and a second-order condition; this states the global minimality those conditions are used for, by integrating the pointwise minimum over $s$.
--
--   Differences from the source:
--   - correction: "A minimizer Q_θ of problem (4) in P(R)" → the minimum is over the floor class {μ ∈ P₂ : μ((−∞,K)) = 0}; reason: the printed claim is false: for u = log, n = 1, Q₁ = δ₂, K₁ = 1 the objective at ½δ₂ + ½δ_t tends to −∞ as t ↓ 0 for every θ; p.11 and p.ec5 make this restriction themselves
--   - encoding: Assumption 2: Q_j(X ∈ [0,K_j]) = 0 with X positive → Q_j((−∞,K_j]) = 0 and K_j > 0; reason: the positivity of X is stated on pp.10–11, so the two sets carry the same mass
--   - encoding: models in P(ℝ) → models in P₂(ℝ); reason: the distance of eq. (1) is an L² norm of quantiles: the paper takes Q ⊂ L²([0,1]), p.26, and writes P₂(ℝ) on p.ec6
--   - encoding: quantile functions on [0,1] → quantiles evaluated on the open interval (0,1); reason: the endpoints are null, and F⁻¹(1) can be infinite; no integral changes
--   - generalization: the floor K* = minᵢ Kᵢ, with θ_c dividing by K_B − K* → any floor K with 0 < K < K_B, with threshold max{|u″(K)|, u′(K)/(K_B − K)}; reason: it specializes to K = K* whenever K* < K_B, and it also covers K* = K_B (for example n = 1), where (EC.11) divides by zero
--   - generalization: continuous quantiles "for simplicity" (p.ec5) → all measures of P₂, with left-continuous quantiles; reason: continuous quantiles are a special case
-- source:
--   Petracou, Xepapadeas, Yannacopoulos, Decision Making under Model Uncertainty: Fréchet-Wasserstein Mean Preferences, manuscript MS-DEC-19-01009-REV (accepted manuscript, hdl.handle.net/11585/863779), Remark EC.1, pp.ec3–ec4

import Mathlib
import Definitions.Def_FrechetPrefs_InadaUtility
import Definitions.Def_FrechetPrefs_Multiplier

open MeasureTheory Set Filter Topology

namespace FrechetPrefs

/-- Remark EC.1, pp.ec3–ec4 of manuscript MS-DEC-19-01009-REV: for `θ` above the threshold, each
pointwise function `x ↦ u(x) + (θ/2)(x − z)²` is strictly convex on `[K,∞)` and is minimized there at a
solution of `ψ(x) = z`. Hence a measure of the floor class whose quantile solves (5) on `(0,1)`
minimizes the objective of (4) on the floor class.

**Formalization Note.** The remark checks a first-order and a second-order condition. The statement
here is the global minimality they are used for. -/
theorem minimality {n : ℕ} (w : Fin n → ℝ) (Q : Fin n → ProbabilityMeasure ℝ) (Kv : Fin n → ℝ)
    (u : ℝ → ℝ) (B : ProbabilityMeasure ℝ) (K : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hQ : ∀ i, Q i ∈ P2)
    (hAss2 : ∀ i, 0 < Kv i ∧ (Q i : Measure ℝ) (Iic (Kv i)) = 0)
    (hu : IsInadaUtility u) (hB : IsBarycenter w Q B)
    (hK0 : 0 < K) (hK : K < KB w Kv) (θ : ℝ)
    (hθ : thetaC u K (KB w Kv) < θ) :
    (∀ z : ℝ, StrictConvexOn ℝ (Ici K) (fun x => u x + θ / 2 * (x - z) ^ 2)) ∧
    (∀ z x : ℝ, K ≤ x → psi u θ x = z →
      IsMinOn (fun y => u y + θ / 2 * (y - z) ^ 2) (Ici K) x) ∧
    (∀ μ ∈ floorClass K,
      (∀ s ∈ Ioo (0 : ℝ) 1, 1 / θ * deriv u (q μ s) + q μ s = q B s) →
      IsMinOn (objective u w Q B θ) (floorClass K) μ) := by sorry

end FrechetPrefs
