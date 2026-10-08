-- Prove2me | Theorems.Thm_GVRPricing_FixedPrice_augmented_le_det
-- name    : GVRPricing.FixedPrice.augmented_le_det
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:03:35.944874+00:00
-- url     : https://prove2.me/theorems/ab4775f6-97bb-42f5-9ff6-6c50dd06025d
-- title:
--   Lemma 1 — J_u(n,t,μ) ≤ J^D(n,t,μ) for every policy u and every μ ≥ 0
-- statement:
--   Let $u$ be an admissible pricing policy, $n$ an initial stock, $t\ge0$ a horizon and $\mu\ge0$. Then the expectations $E_u[\int_0^t r(\lambda_s)\,ds]$ and $E_u[\int_0^t\lambda_s\,ds]$ are finite, and
--   $$J_u(n,t,\mu)\le J^D(n,t,\mu),$$
--   where $J_u(n,t,\mu)$ is the augmented functional (15) and $J^D(n,t,\mu)$ the augmented deterministic value (16).
--
--   The stochastic augmented functional never beats the best deterministic rate path once the stock constraint is priced at $\mu$. With (15) this gives $J^*(n,t)\le\inf_{\mu\ge0}J^D(n,t,\mu)$.
--
--   **Formalization Note** The finiteness of both expectations is part of the conclusion, so the real-valued $J_u(n,t,\mu)$ is the paper's quantity and not a truncation. The statement covers every stock $n$, including $n=0$, and every horizon $t\ge0$.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1007 (PDF 9), §3.2.1, Lemma 1

import Mathlib
import Definitions.Def_GVRPricing_FixedPrice_Model
import Definitions.Def_GVRPricing_FixedPrice_SalesProcess
import Definitions.Def_GVRPricing_FixedPrice_Deterministic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GVRPricing.FixedPrice

/-- **Lemma 1** (p. 1007): `J_u(n, t, μ) ≤ J^D(n, t, μ)` for every admissible policy `u` and
every `μ ≥ 0` (here for every stock `n` and horizon `t ≥ 0`). The two expectations that make up
`J_u(n, t, μ)` are asserted finite, so the real-valued functional is the paper's. -/
theorem augmented_le_det (M : Model) (u : Policy M) (n : ℕ) (t μ : ℝ) (ht : 0 ≤ t)
    (hμ : 0 ≤ μ) :
    u.expectedRevenueRate n t ≠ ∞ ∧ u.expectedCumIntensity n t ≠ ∞ ∧
    u.augmentedValue n t μ ≤ detAugValue M n t μ := by sorry

end GVRPricing.FixedPrice
