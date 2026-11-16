-- Prove2me | Theorems.Thm_MultiSpinCounting_Positive_Supplement_theorem_1_2
-- name    : MultiSpinCounting.Positive.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:26:15.611726+00:00
-- url     : https://prove2.me/theorems/dffce7e6-7c0d-42cf-8012-6b3b96c402a4
-- title:
--   Theorem 1.2 (companion theorem; not used in the proof of the goal) — strong spatial mixing
-- statement:
--   Fix $K\ge1$, $\alpha\ge0$, $D\ge1$, and $c>0$ with $Dc<1$. Choose, before the palette size and all instances,
--   $$C_*=\frac{KD(4\operatorname{artanh}c)}{4Dc(1-Dc)}>0.$$
--   For every integer $q\ge3$, every positive real $q$-spin instance on an $n\ge1$ vertex graph with $S_\ell(G)\le Kn^\alpha D^\ell$ for every $\ell\ge0$, and $c_B(A_e)\le c$ on every edge, consider two assignments $\sigma,\tau$ on a boundary $\Lambda$ and $v\notin\Lambda$. Set $\Delta=\{u\in\Lambda:\sigma_u\ne\tau_u\}$ and $r=\operatorname{dist}_G(v,\Delta)$. Then
--   $$\|\mu_\Phi(v\leftarrow\cdot\mid\Lambda\leftarrow\sigma)-\mu_\Phi(v\leftarrow\cdot\mid\Lambda\leftarrow\tau)\|_{\rm TV}\le C_*n^\alpha(Dc)^r\quad(r<\infty).$$
--   If $r=\infty$, the two conditional marginal vectors are equal. The coefficient is independent of $q$, $n$, the instance, and the boundary conditions. This yields the whole polynomial-prefactor spatial-mixing statement; at $\alpha=0$ the prefactor is constant, giving uniform strong spatial mixing.
--
--   Differences from the source:
--   - encoding: a graph family satisfying (1.4) → the pointwise published WalkBound for each full-active graph on Fin n; reason: a bound uniform over every such instance is the equivalent family statement
--   - generalization: feasible boundary assignments → all assignments on the boundary; reason: strictly positive real data and q ≥ 3 imply positive weight for every conditioning event
--   - encoding: a coefficient C∗ depending only on K, α, D, c → C∗ = KD(4 artanh c)/(4Dc(1−Dc)) before q and the instance; reason: this is the coefficient supplied by the proof on p. 12
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), p. 4, Theorem 1.2

import Mathlib
import Definitions.Def_MultiSpinCounting_Positive_Supplement_Metrics
import Definitions.Def_MultiSpinCounting_Positive_Supplement_Conditioning

namespace MultiSpinCounting.Positive.Supplement

/-- Theorem 1.2, p. 4. The proof on p. 12 supplies the displayed coefficient.
It is uniform in q and the instance, and the disconnected case is included. -/
theorem theorem_1_2 (K α D c : ℝ) (hK : 1 ≤ K) (hα : 0 ≤ α)
    (hD : 1 ≤ D) (hc : 0 < c) (hDc : D * c < 1) :
    ∃ Cstar : ℝ, 0 < Cstar ∧
      Cstar = K * D * (4 * Real.artanh c) / (4 * (D * c) * (1 - D * c)) ∧
      ∀ q : ℕ, 3 ≤ q → ∀ n : ℕ, 0 < n → ∀ Φ : Instance n q ℝ,
      Φ.active = Finset.univ → IsPositive Φ → WalkBound Φ n K α D →
      (∀ e ∈ edges Φ, cB (Φ.interaction e.1 e.2) ≤ c) →
      ∀ (Λ : Finset (Fin n)) (σ τ : Fin n → Fin q) (v : Fin n), v ∉ Λ →
      let r := discrepancyDist Φ.graph Λ σ τ v
      (r ≠ ⊤ → tvDist (condMarginal Φ Λ σ v) (condMarginal Φ Λ τ v) ≤
        Cstar * (n : ℝ) ^ α * (D * c) ^ r.toNat) ∧
      (r = ⊤ → condMarginal Φ Λ σ v = condMarginal Φ Λ τ v) := by sorry

end MultiSpinCounting.Positive.Supplement
