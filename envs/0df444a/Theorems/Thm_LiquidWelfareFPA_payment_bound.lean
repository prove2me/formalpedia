-- Prove2me | Theorems.Thm_LiquidWelfareFPA_payment_bound
-- name    : LiquidWelfareFPA.payment_bound
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T05:36:09.58631+00:00
-- url     : https://prove2.me/theorems/4c2169bc-e353-481a-a523-533f70c94aa1
-- title:
--   Payment bound $0\le P_i\le\mathrm{LW}_i+\mathrm{Reg}^+/\gamma$ on the competitive-ratio event
-- statement:
--   In an outcome with nonnegative budgets and a tie rule, suppose player $i$ has competitive ratio at most $\gamma\ge1$ and regret at most $\mathrm{Reg}$. Then
--
--   $$0\ \le\ P_i\ \le\ \mathrm{LW}_i+\frac{\max\{\mathrm{Reg},0\}}{\gamma},\qquad \mathrm{LW}_i=\min\{B_i,V_i\}.$$
--
--   The bound follows from $P_i\le B_i$ and from $V_i-P_i\ge-\mathrm{Reg}/\gamma$, since $\hat U_i(\mu)\ge0$. It is the step of the proof of Theorem 4.2 that turns payments back into liquid welfare.
--
--   Differences from the source:
--   - generalization: 0 ≤ P_i ≤ LW_i + Reg/γ with Reg (the text uses Reg ≥ 0 tacitly) → 0 ≤ P_i ≤ LW_i + Reg/γ with Reg⁺ = max{Reg, 0} in the regret term coming from (7), for any Reg (≥ −1 where aggregated); reason: Reg⁺ = Reg for Reg ≥ 0, so this is the printed statement there; for Reg < 0 the form with Reg itself fails (the instance of the goal's correction with Reg = −1/2 gives P_i = 1 > 1/2 = LW_i + Reg/γ), and the form with Reg⁺ is what the proof of Theorem 4.2 needs
--   - encoding: values and prices of the auction; budgets, bids and the tie rule left implicit → an outcome of the first-price auction (values in [0,1], bids ≥ 0, winner any highest bidder, price = winner's bid), budgets B_i ≥ 0, any tie rule; d_it := 0 when n = 1; reason: the model of §3; the proof uses d_it ≤ p_t, which holds in it (p.7)
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, proof of Theorem 4.2, p.9

import Mathlib
import Definitions.Def_LiquidWelfareFPA_IsTieRule
import Definitions.Def_LiquidWelfareFPA_CR

namespace LiquidWelfareFPA

/-- **Payment bound `0 ≤ P_i ≤ LW_i + Reg/γ` on the competitive-ratio event.**
Fikioris & Tardos, arXiv:2210.07502v4, proof of Theorem 4.2, p.9: "We now use the fact that for
all i, 0 ≤ P_i ≤ LW_i + Reg/γ, which follows from P_i ≤ B_i (otherwise player i would have
unbounded negative utility) and V_i − P_i ≥ −Reg/γ (because of the competitive ratio guarantee
and that for any µ, Û(µ) ≥ 0)."

If player `i` has competitive ratio at most `γ ≥ 1` and regret at most `Reg`, then
`0 ≤ P_i ≤ min{B_i, V_i} + max{Reg, 0}/γ`.

**Formalization Note** `Reg⁺ = max Reg 0` replaces `Reg`; the two agree for `Reg ≥ 0`, which the
text uses tacitly, and the statement also covers `Reg < 0`. -/
theorem payment_bound {n T : ℕ} (B : Fin n → ℝ) (hB : ∀ i, 0 ≤ B i) (o : Outcome n T)
    (win : Fin n → Fin T → ℝ → Prop) (hwin : IsTieRule o win) (γ Reg : ℝ) (hγ : 1 ≤ γ)
    (i : Fin n) (hCR : CR B o win γ Reg i) :
    0 ≤ o.pay i ∧ o.pay i ≤ min (B i) (o.val i) + max Reg 0 / γ := by sorry

end LiquidWelfareFPA
