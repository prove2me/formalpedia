-- Prove2me | Theorems.Thm_MitigateSupplyRisk_DualSourcing_eq6_first_order
-- name    : MitigateSupplyRisk.DualSourcing.eq6_first_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:47.821363+00:00
-- url     : https://prove2.me/theorems/854f8126-fb75-46c1-9091-9f3e49c1fc8c
-- title:
--   §4.1, Eq. (6), p. 494 — the partial derivative of Π₂ in q_i and the interior first-order condition
-- statement:
--   Consider the two-supplier random-capacity newsvendor with expected profit $\Pi_2(q; a)$, and suppose that demand $X \ge 0$ has a density, finite mean and distribution function $F$. Fix a supplier $i$, let $j$ be the other supplier, and let $q \ge 0$ with $0 < q_i < K_i$. Write $y_j = \min\{q_j, (K_j - \xi_j)^+\}$ with $\xi_j \sim \nu_j(a_j)$.
--
--   1. The partial derivative of $\Pi_2$ in $q_i$ at $q$ is
--   $$\nabla_{q_i} \Pi_2(q; a) = (r + p - v)\Big(\psi_i + G_i(K_i - q_i, a_i)\big(\phi_i - \mathbb E_{\xi_j}[F(q_i + y_j)]\big)\Big).$$
--   2. Consequently, if $q$ is optimal, its interior coordinate satisfies the first-order condition (6):
--   $$\psi_i + G_i(K_i - q_i, a_i)\big(\phi_i - \mathbb E_{\xi_j}[F(q_i + y_j)]\big) = 0.$$
--
--   Here $G_i(K_i - q_i, a_i)$ is the probability that supplier $i$'s effective capacity exceeds the order, so that a marginal unit ordered from $i$ is delivered, and $\mathbb E[F(q_i + y_j)]$ is the probability that such a unit is not needed to meet demand. The condition (6) is the generalization of the critical-fractile condition to two unreliable suppliers.
--
--   **Formalization Note.** The paper states (6) for the optimal interior quantity at the initial indices $a^0$; it holds at any indices $a$, which is how it is stated here. The paper drops the positive factor $r + p - v$, which is harmless in "$= 0$" but is kept in the derivative formula.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 494 (PDF p. 6), §4.1, Eq. (6)

import Mathlib
import Definitions.Def_MitigateSupplyRisk_DualSourcing_Model

open MeasureTheory ProbabilityTheory

namespace MitigateSupplyRisk.DualSourcing

/-- Eq. (6) (Wang, Gilland, Tomlin 2010, §4.1, p. 494). Let demand have a density, with
distribution function `F`. For a feasible `q` with `0 < q_i < K_i` and `j ≠ i` the other
supplier:
1. the partial derivative of `Π₂(·; a)` in `q_i` at `q` is
   `(r + p − v)(ψ_i + G_i(K_i − q_i, a_i)(φ_i − E_{ξ_j}[F(q_i + y_j)]))`, where
   `y_j = min{q_j, (K_j − ξ_j)⁺}` and `ξ_j` has law `ν_j(a_j)`;
2. if `q` is optimal, then `ψ_i + G_i(K_i − q_i, a_i)(φ_i − E_{ξ_j}[F(q_i + y_j)]) = 0`. -/
theorem eq6_first_order (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hμint : Integrable id μ) (hμac : μ ≪ volume)
    (a q : Fin 2 → ℝ) (hq : q ∈ Model.orders) (i j : Fin 2) (hij : i ≠ j)
    (hqi0 : 0 < q i) (hqiK : q i < M.K i) :
    HasDerivAt (fun t => M.Pi2 μ (Function.update q i t) a)
      ((M.r + M.p - M.v) * (M.psi i + M.G i (M.K i - q i) (a i) *
        (M.phi i - ∫ s, cdf μ (q i + Model.deliv (M.K j) (q j) s) ∂(M.ν j (a j))))) (q i) ∧
    (M.IsOptimal μ a q →
      M.psi i + M.G i (M.K i - q i) (a i) *
        (M.phi i - ∫ s, cdf μ (q i + Model.deliv (M.K j) (q j) s) ∂(M.ν j (a j))) = 0) := by sorry

end MitigateSupplyRisk.DualSourcing
