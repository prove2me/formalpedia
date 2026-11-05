-- Prove2me | Theorems.Thm_LiquidWelfareFPA_eq_2
-- name    : LiquidWelfareFPA.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:17.941532+00:00
-- url     : https://prove2.me/theorems/8beb1998-b932-4057-b749-6c19c6ba61d8
-- title:
--   Inequality (2) — per-player value bound on the competitive-ratio event
-- statement:
--   In an outcome with nonnegative budgets and a tie rule, suppose player $i$ has competitive ratio at most $\gamma\ge1$ and regret at most $\mathrm{Reg}$. Then
--
--   $$V_i\ \ge\ \frac1\gamma\sup_{\mu\in[0,1]}\hat U_i(\mu)-\frac{\mathrm{Reg}}\gamma+P_i ,$$
--
--   and, for every set of rounds $O\subseteq[T]$ with $\mathrm{LW}^*_i=\min\{B_i,\sum_{t\in O}v_{it}\}$ and every $\lambda\in(0,1)$,
--
--   $$V_i\ \ge\ \frac1\gamma\min\Big\{\frac{1-\lambda}{\lambda}\,\mathrm{LW}^*_i,\ c(\lambda)\lambda\,\mathrm{LW}^*_i-c(\lambda)\sum_{t\in O}p_t\Big\}-\frac{\mathrm{Reg}+1}\gamma+P_i .$$
--
--   This is display (2) of the proof of Theorem 4.2: the competitive ratio combined with Lemma 4.1.
--
--   Differences from the source:
--   - generalization: O_i is player i's bundle in the allocation maximizing liquid welfare, LW*_i = min{B_i, Σ_{t∈O_i} v_it} → any set of rounds O ⊆ [T], with min{B_i, Σ_{t∈O} v_it} in place of LW*_i; reason: the proof uses only Σ_{t∈O_i} v_it ≥ LW*_i and B_i ≥ LW*_i; taking O = O_i gives the printed lemma
--   - encoding: V_i = U_i + P_i with U_i the budgeted quasi-linear utility → P_i ≤ B_i and the competitive-ratio inequality (the event CR), whose second clause is the first line; reason: on the event, U_i = V_i − P_i is finite
--   - encoding: values and prices of the auction; budgets, bids and the tie rule left implicit → an outcome of the first-price auction (values in [0,1], bids ≥ 0, winner any highest bidder, price = winner's bid), budgets B_i ≥ 0, any tie rule; d_it := 0 when n = 1; reason: the model of §3; the proof uses d_it ≤ p_t, which holds in it (p.7)
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, proof of Theorem 4.2, (2), p.8

import Mathlib
import Definitions.Def_LiquidWelfareFPA_IsTieRule
import Definitions.Def_LiquidWelfareFPA_CR
import Definitions.Def_LiquidWelfareFPA_cfun

namespace LiquidWelfareFPA

/-- **Inequality (2): per-player value bound on the competitive-ratio event.**
Fikioris & Tardos, arXiv:2210.07502v4, proof of Theorem 4.2, (2), p.8: "If player i has
competitive ratio at most γ and regret at most Reg, it holds that V_i = U_i + P_i ≥ (1/γ)
sup_{µ∈[0,1]} Û_i(µ) − Reg/γ + P_i ≥ (1/γ) min{(1−λ)/λ LW*_i, c(λ)λLW*_i − c(λ)∑_{t∈O_i} p_t}
− (Reg+1)/γ + P_i".

If player `i` has competitive ratio at most `γ ≥ 1` and regret at most `Reg` in the outcome `o`,
then for every set of rounds `O`, with `LW*_i := min{B_i, ∑_{t∈O} v_it}`, and every `λ ∈ (0,1)`,
both inequalities of (2) hold.

**Formalization Note** `O` is arbitrary (the printed display uses the optimal bundle `O_i`). -/
theorem eq_2 {n T : ℕ} (B : Fin n → ℝ) (hB : ∀ i, 0 ≤ B i) (o : Outcome n T)
    (win : Fin n → Fin T → ℝ → Prop) (hwin : IsTieRule o win) (γ Reg : ℝ) (hγ : 1 ≤ γ)
    (i : Fin n) (hCR : CR B o win γ Reg i) (O : Finset (Fin T)) (lam : ℝ) (hlam0 : 0 < lam)
    (hlam1 : lam < 1) :
    1 / γ * bench B o win i - Reg / γ + o.pay i ≤ o.val i ∧
      1 / γ * min ((1 - lam) / lam * min (B i) (∑ t ∈ O, o.v i t))
          (cfun lam * lam * min (B i) (∑ t ∈ O, o.v i t) - cfun lam * ∑ t ∈ O, o.price t)
        - (Reg + 1) / γ + o.pay i ≤ o.val i := by sorry

end LiquidWelfareFPA
