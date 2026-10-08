-- Prove2me | Theorems.Thm_GVRPricing_FixedPrice_augmented_ge_revenue
-- name    : GVRPricing.FixedPrice.augmented_ge_revenue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:59:55.295613+00:00
-- url     : https://prove2.me/theorems/73d3b21b-fb17-44a7-8a9b-7a9902101961
-- title:
--   Eq. (15) — the augmented functional J_u(n,t,μ) dominates J_u(n,t) for μ ≥ 0
-- statement:
--   Let $u$ be an admissible pricing policy, $n$ an initial stock, $t\ge0$ a horizon and $\mu\ge0$ a multiplier. Then the expected revenue $J_u(n,t)$ is finite and
--   $$J_u(n,t,\mu)=E_u\Big[\int_0^t\big(r(\lambda_s)-\mu\lambda_s\big)ds\Big]+n\mu\ \ge\ J_u(n,t).\qquad(15)$$
--
--   The term $n\mu$ prices the stock constraint (13). Combined with Lemma 1, this inequality bounds every policy's revenue by the Lagrangian dual function of the deterministic problem.
--
--   **Formalization Note** $J_u(n,t,\mu)$ is the real number $E_u[\int_0^t r(\lambda_s)ds]-\mu E_u[\int_0^t\lambda_s ds]+n\mu$; finiteness of the two expectations is asserted in Lemma 1. Here the statement asserts that $J_u(n,t)\neq\infty$ before comparing real values.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1007 (PDF 9), §3.2.1, Proof of Theorem 2, eq. (15)

import Mathlib
import Definitions.Def_GVRPricing_FixedPrice_Model
import Definitions.Def_GVRPricing_FixedPrice_SalesProcess

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GVRPricing.FixedPrice

/-- **Eq. (15)** (§3.2.1, p. 1007): for every admissible policy `u`, stock `n`, horizon `t ≥ 0`
and multiplier `μ ≥ 0`, the expected revenue `J_u(n, t)` is finite and bounded by the augmented
functional `J_u(n, t, μ) = E_u[∫_0^t (r(λ_s) − μ λ_s) ds] + n μ`. -/
theorem augmented_ge_revenue (M : Model) (u : Policy M) (n : ℕ) (t μ : ℝ) (ht : 0 ≤ t)
    (hμ : 0 ≤ μ) :
    u.expectedRevenue n t ≠ ∞ ∧ (u.expectedRevenue n t).toReal ≤ u.augmentedValue n t μ := by sorry

end GVRPricing.FixedPrice
