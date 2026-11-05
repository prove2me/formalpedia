-- Prove2me | Theorems.Thm_LiquidWelfareFPA_aggregate_bound
-- name    : LiquidWelfareFPA.aggregate_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:34.37459+00:00
-- url     : https://prove2.me/theorems/6c2b7508-e268-4949-a373-a766a25b7991
-- title:
--   Proof of Theorem 4.2, p.9 — $\mathrm{LW}^*-\ldots\le\max\{1+\frac1\lambda,\ldots\}\mathrm{LW}$ for every $\lambda\in(0,1)$ (corrected: $\mathrm{Reg}\ge-1$)
-- statement:
--   In an outcome with nonnegative budgets and a tie rule, suppose every player has competitive ratio at most $\gamma\ge1$ and regret at most $\mathrm{Reg}\ge-1$. Then for every $\lambda\in(0,1)$
--
--   $$\mathrm{LW}^*-\max\Big\{\frac{\lambda}{1-\lambda},\frac1{c(\lambda)\lambda}\Big\}\,n\,(\mathrm{Reg}+1)-\frac{n}{\gamma\lambda}\,\mathrm{Reg}^+\ \le\ \max\Big\{1+\frac1\lambda,\ \frac{\gamma\lambda}{1-\lambda},\ \frac{\gamma}{c(\lambda)\lambda}\Big\}\,\mathrm{LW},$$
--
--   where $\mathrm{Reg}^+=\max\{\mathrm{Reg},0\}$ and $\mathrm{LW}^*$ is the optimal liquid welfare.
--
--   This is the last display of p.9: it bounds the price of anarchy by a maximum of three explicit functions of $\lambda$, which the rest of the proof minimizes.
--
--   Differences from the source:
--   - correction: Reg with no stated sign → −1 ≤ Reg; reason: false for Reg < −1: on the family of Theorem 4.2's correction (n = 2, γ = 1, LW = LW* = 2, both events hold with Reg → −∞) the left side is at least 2 + 2 max{λ/(1−λ), 1/(c(λ)λ)}(−Reg − 1), which exceeds the fixed right side; the aggregation of the (Reg+1)-terms over |Y|, |Z| ≤ n needs Reg + 1 ≥ 0
--   - generalization: LW* − max{λ/(1−λ), 1/(c(λ)λ)} n(Reg+1) − (n/(γλ)) Reg ≤ … with Reg (the text uses Reg ≥ 0 tacitly) → LW* − max{λ/(1−λ), 1/(c(λ)λ)} n(Reg+1) − (n/(γλ)) Reg ≤ … with Reg⁺ = max{Reg, 0} in the regret term coming from (7), for any Reg (≥ −1 where aggregated); reason: Reg⁺ = Reg for Reg ≥ 0, so this is the printed statement there; for Reg ∈ [−1, 0) the form with Reg itself fails (n = 2, T = 2, γ = 2, Reg = −1, B₁ = B₂ = 1/100, all bids 0, v₁₁ = v₂₂ = 1, v₁₂ = v₂₁ = 0, player 1 wins round 1 and player 2 round 2: V_i − P_i = 1 ≥ (sup Û_i + 1)/2, so both events hold, but at λ = 1/2 its left side is 2.02 and its right side 0.06), and the form with Reg⁺ is what the proof of Theorem 4.2 needs
--   - encoding: values and prices of the auction; budgets, bids and the tie rule left implicit → an outcome of the first-price auction (values in [0,1], bids ≥ 0, winner any highest bidder, price = winner's bid), budgets B_i ≥ 0, any tie rule; d_it := 0 when n = 1; reason: the model of §3; the proof uses d_it ≤ p_t, which holds in it (p.7)
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, proof of Theorem 4.2, p.9, last display

import Mathlib
import Definitions.Def_LiquidWelfareFPA_IsTieRule
import Definitions.Def_LiquidWelfareFPA_CR
import Definitions.Def_LiquidWelfareFPA_LW
import Definitions.Def_LiquidWelfareFPA_LWstar
import Definitions.Def_LiquidWelfareFPA_cfun

namespace LiquidWelfareFPA

/-- **The aggregated liquid-welfare inequality, for every `λ ∈ (0,1)`.**
Fikioris & Tardos, arXiv:2210.07502v4, proof of Theorem 4.2, p.9, last display: "Plugging (7)
into (6) we get LW* − max{λ/(1−λ), 1/(c(λ)λ)} n(Reg + 1) − (n/(γλ)) Reg ≤ … ≤
max{1 + 1/λ, γλ/(1−λ), γ/(c(λ)λ)} LW."

If every player has competitive ratio at most `γ ≥ 1` and regret at most `Reg ≥ −1` in the outcome
`o`, then for every `λ ∈ (0,1)`
`LW* − max{λ/(1−λ), 1/(c(λ)λ)}·n·(Reg+1) − (n/(γλ))·max{Reg,0} ≤ max{1+1/λ, γλ/(1−λ), γ/(c(λ)λ)}·LW`.

**Formalization Note** `max Reg 0` replaces `Reg` in the term coming from (7); they agree for
`Reg ≥ 0`. `Reg ≥ −1` is what the aggregation of the `(Reg+1)`-terms over at most `n` players
needs. -/
theorem aggregate_bound {n T : ℕ} (B : Fin n → ℝ) (hB : ∀ i, 0 ≤ B i) (o : Outcome n T)
    (win : Fin n → Fin T → ℝ → Prop) (hwin : IsTieRule o win) (γ Reg : ℝ) (hγ : 1 ≤ γ)
    (hReg : -1 ≤ Reg) (hCR : ∀ i, CR B o win γ Reg i) (lam : ℝ) (hlam0 : 0 < lam)
    (hlam1 : lam < 1) :
    LWstar B o - max (lam / (1 - lam)) (1 / (cfun lam * lam)) * n * (Reg + 1)
        - n / (γ * lam) * max Reg 0
      ≤ max (max (1 + 1 / lam) (γ * lam / (1 - lam))) (γ / (cfun lam * lam)) * LW B o := by sorry

end LiquidWelfareFPA
