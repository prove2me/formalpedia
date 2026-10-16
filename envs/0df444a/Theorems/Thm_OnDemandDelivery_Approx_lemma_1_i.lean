-- Prove2me | Theorems.Thm_OnDemandDelivery_Approx_lemma_1_i
-- name    : OnDemandDelivery.Approx.lemma_1_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:48.274517+00:00
-- url     : https://prove2.me/theorems/b841e3f8-513e-493b-ab5d-172469e3eb20
-- title:
--   Lemma 1(i), p. 12 — the cost-to-go ℋ_n(ℐ^n, q^n, ζ^n) is nondecreasing in the driver status ζ^n
-- statement:
--   Consider the dispatching and routing model under its standing assumptions and a period $1 \le n \le N$. For every realized demand $(\mathcal I^n, q^n)$ and driver statuses $\zeta^n_1, \zeta^n_2$ with $\zeta^n_1 \ge \zeta^n_2$ componentwise,
--   $$\mathcal H_n(\mathcal I^n, q^n, \zeta^n_1) \ge \mathcal H_n(\mathcal I^n, q^n, \zeta^n_2).$$
--
--   More drivers en route can only increase the optimal expected cost; this is the structural property the approximation APT is designed to share (part (ii) of the lemma).
--
--   **Formalization Note.** "$\zeta^n_1 \ge \zeta^n_2$" is the componentwise order on status vectors indexed by all periods. Values are in $[0,\infty]$.
-- source:
--   Liu, Luo, On-Demand Delivery from Stores: Dynamic Dispatching and Routing with Random Demand, arXiv:2107.13058v3, p. 12, Lemma 1(i)

import Mathlib
import Definitions.Def_OnDemandDelivery_Approx_Setting

open scoped ENNReal NNReal

namespace OnDemandDelivery.Approx
open Model
theorem lemma_1_i {L : Type*} [Fintype L] (M : Model L) (hM : M.Standing) (n : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ M.N) (d : Demand L) (ζ₁ ζ₂ : ℕ → ℕ) (h : ζ₂ ≤ ζ₁) :
    M.H n d ζ₂ ≤ M.H n d ζ₁ := by sorry
end OnDemandDelivery.Approx
