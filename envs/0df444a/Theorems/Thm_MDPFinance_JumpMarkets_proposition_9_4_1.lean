-- Prove2me | Theorems.Thm_MDPFinance_JumpMarkets_proposition_9_4_1
-- name    : MDPFinance.JumpMarkets.proposition_9_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:28:52.516792+00:00
-- url     : https://prove2.me/theorems/b5e0006f-b8eb-4aa7-8dea-209d5527a1de
-- title:
--   Proposition 9.4.1 — the trade execution model's bounding function and contraction
-- statement:
--   **Proposition 9.4.1** (p. 295). The function $b(t,x) := C(x)$ is a bounding function for
--   the discrete-time model and $\alpha_b \le 1 - e^{-\lambda T} < 1$, i.e. the discrete-time Markov
--   Decision Model is contracting.
--
--   The cost function is its own bounding function — the cleanest possible choice, and it works because
--   $|c(t,x,\alpha)| \le C(x)$ follows from $\alpha_s \le x$ and monotonicity of $C$ alone.
--
--   **The module is $1 - e^{-\lambda T}$, and the bound is strict for every finite horizon.** The gap
--   from $1$ is exactly the probability $e^{-\lambda T}$ that no trading epoch arrives at all, in which
--   case the whole inventory is dumped at $T$ and nothing is discounted away. So the contraction is
--   genuinely driven by the illiquidity: the rarer the trading epochs, the weaker the contraction.
--
--   Unlike §9.3's Proposition 9.3.2 no auxiliary parameter $\gamma$ is needed, because the one-stage
--   cost is already dominated by $C(x)$ — the trade execution problem has a bounded reward structure
--   relative to its own state, which §9.3's unbounded utility does not.
--
--   **Moderation note.** Checked against p. 295; unchanged.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 295 (PDF 305), Proposition 9.4.1

import Mathlib
import Definitions.Def_MDPFinance_JumpMarkets_TradeExecution

open MeasureTheory

namespace MDPFinance.JumpMarkets

/-- **Proposition 9.4.1** (p. 295). `b(t,x) := C(x)` is a bounding function for the
discrete-time model and `α_b ≤ 1 - e^{-λT} < 1`: the model is contracting. -/
theorem proposition_9_4_1 (M : TradeExecution) :
    M.IsBoundingFunction (1 - Real.exp (-M.lam * M.T)) ∧
    1 - Real.exp (-M.lam * M.T) < 1 := by sorry

end MDPFinance.JumpMarkets
