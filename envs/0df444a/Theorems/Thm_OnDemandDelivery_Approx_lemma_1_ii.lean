-- Prove2me | Theorems.Thm_OnDemandDelivery_Approx_lemma_1_ii
-- name    : OnDemandDelivery.Approx.lemma_1_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:44.329265+00:00
-- url     : https://prove2.me/theorems/b3217728-5620-40f1-a788-844af073d9a4
-- title:
--   Lemma 1(ii), p. 12 — for nonnegative ω, the APT value V^n_APT(ζ^n) is nondecreasing in ζ^n
-- statement:
--   Consider the dispatching and routing model under its standing assumptions, a period $1 \le n \le N$ and any nonnegative APT parameters $\{\omega^{n'}_m(K^m)\}$. For driver statuses $\zeta^n_1 \ge \zeta^n_2$ componentwise,
--   $$V^n_{APT}(\zeta^n_1) \ge V^n_{APT}(\zeta^n_2).$$
--
--   The approximation thus keeps the monotonicity of the true value function in the driver status (part (i) of the lemma).
--
--   **Formalization Note.** Nonnegativity of the parameters is built into their type ($\mathbb R_{\ge 0}$). $V^n_{APT}$ is in $[0,\infty]$ and is $+\infty$ when APT is infeasible.
-- source:
--   Liu, Luo, On-Demand Delivery from Stores: Dynamic Dispatching and Routing with Random Demand, arXiv:2107.13058v3, p. 12, Lemma 1(ii)

import Mathlib
import Definitions.Def_OnDemandDelivery_Approx_Setting

open scoped ENNReal NNReal

namespace OnDemandDelivery.Approx
open Model
theorem lemma_1_ii {L : Type*} [Fintype L] (M : Model L) (hM : M.Standing) (n : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ M.N) (ω : ℕ → ℕ → ℕ → ℝ≥0) (ζ₁ ζ₂ : ℕ → ℕ) (h : ζ₂ ≤ ζ₁) :
    M.Vapt n ζ₂ ω ≤ M.Vapt n ζ₁ ω := by sorry
end OnDemandDelivery.Approx
