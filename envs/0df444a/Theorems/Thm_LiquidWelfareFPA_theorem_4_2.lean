-- Prove2me | Theorems.Thm_LiquidWelfareFPA_theorem_4_2
-- name    : LiquidWelfareFPA.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:33.585468+00:00
-- url     : https://prove2.me/theorems/909d6db7-f16e-4750-a6df-8d999ac62737
-- title:
--   Theorem 4.2 — $\mathrm{LW}\ge(\mathrm{LW}^*-O(n)(\mathrm{Reg}+1))/(\gamma+1/2+O(1/\gamma))$ with probability $\ge1-n\delta$ (corrected: $\mathrm{Reg}\ge-1$)
-- statement:
--   There are absolute constants $C\ge0$ and $K\ge0$ with the following property. Let $n,T\in\mathbb N$, $\gamma\ge1$, $\mathrm{Reg}\ge-1$ and $\delta\ge0$, and let $B_1,\dots,B_n\ge0$ be budgets. Consider any random run of $T$ sequential first-price auctions among $n$ players on a probability space $(\Omega,\mathbb P)$: values $v_{it}\in[0,1]$, bids $b_{it}\ge0$, each item won by a highest bidder at her bid, together with any (possibly random) tie rule for the benchmark. Suppose that, for every player $i$,
--
--   $$\mathbb P\big(\text{player } i \text{ does not have competitive ratio at most }\gamma\text{ and regret at most }\mathrm{Reg}\big)\le\delta .$$
--
--   Then
--
--   $$\mathbb P\left(\mathrm{LW}\ <\ \frac{\mathrm{LW}^*-C\,n\,(\mathrm{Reg}+1)}{\gamma+\tfrac12+K/\gamma}\right)\ \le\ n\delta .$$
--
--   In words: if every budgeted buyer learns well enough to be $\gamma$-competitive against the best fixed shading multiplier, the liquid welfare of sequential first-price auctions is within a factor $\gamma+1/2+O(1/\gamma)$ of optimal, up to an additive regret term — about $2.41$ for no-regret buyers ($\gamma=1$).
--
--   **Formalization Note** The probability space may live in any universe. Probabilities are those of the measure on arbitrary sets (outer measure); no measurability or independence across players is assumed. The constants $C,K$ are chosen before every other quantity.
--
--   Differences from the source:
--   - correction: Reg arbitrary → Reg ≥ −1; reason: false for Reg < −1 whenever C > 0 (and C = 0 already fails at Reg ≥ 0: two players bid 0, the item goes to player 1 of value 0, player 2 has value 1 and budget 1, so LW = 0 < LW*/(γ + 1/2 + K/γ) with Reg = T): n = 2, γ = 1, B₁ = B₂ = 1, T = 2k, player 1 wins rounds 1..k at prices c/t + η and player 2 the rest symmetrically (c = 0.99/H_k, η = 0.01/k), so P_i = 1, V_i = k, LW = LW* = 2, U_i − sup Û_i ≥ kc/(1+c) − 3 → ∞; with Reg := −(U_i − sup Û_i) both players satisfy the assumption surely (δ = 0) while 2 ≥ (2 + 2C(−Reg − 1))/(γ + 1/2 + K/γ) fails for large k
--   - reading: LW* − O(n)(Reg + 1) and γ + 1/2 + O(1/γ) → LW* − C·n·(Reg + 1) and γ + 1/2 + K/γ with absolute constants C, K ≥ 0 chosen before n, T, γ, Reg, δ and the instance; reason: the strongest reading of the O's, uniform over all parameters
--   - reading: with probability at least 1 − δ (resp. 1 − nδ) → the failure event has (outer) probability at most δ (resp. nδ); no measurability assumed; reason: equivalent for measurable events; the union bound needs nothing more
--   - generalization: for any δ > 0 → for any δ ≥ 0; reason: δ = 0 is included; δ > 0 is a special case
--   - generalization: values v_it of the model fixed in advance → values, bids, winners and the tie rule may all depend on ω; reason: random values are allowed by the paper's adaptive adversary (p.14); fixed values are the special case of constant functions
--   - encoding: values and prices of the auction; budgets, bids and the tie rule left implicit → an outcome of the first-price auction (values in [0,1], bids ≥ 0, winner any highest bidder, price = winner's bid), budgets B_i ≥ 0, any tie rule; d_it := 0 when n = 1; reason: the model of §3; the proof uses d_it ≤ p_t, which holds in it (p.7)
--   - encoding: the allocation maximizing liquid welfare → LW* is the maximum over allocations of the T items, items may stay unallocated; reason: values are nonnegative, so the optimum is the same
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, Theorem 4.2, p.8

import Mathlib
import Definitions.Def_LiquidWelfareFPA_IsTieRule
import Definitions.Def_LiquidWelfareFPA_CR
import Definitions.Def_LiquidWelfareFPA_LW
import Definitions.Def_LiquidWelfareFPA_LWstar

namespace LiquidWelfareFPA

/-- **Theorem 4.2 (liquid welfare of γ-competitive buyers in sequential first-price auctions).**
Fikioris & Tardos, arXiv:2210.07502v4, Theorem 4.2, p.8: "Assume that every player i has
competitive ratio at most γ ≥ 1 and regret Reg with probability at least 1 − δ. Then
LW ≥ (LW* − O(n)(Reg + 1))/(γ + 1/2 + O(1/γ)) with probability at least 1 − nδ, for any δ > 0."

There are absolute constants `C, K ≥ 0` such that for all `n, T`, every `γ ≥ 1`, every
`Reg ≥ −1`, every `δ ≥ 0`, all nonnegative budgets `B`, every probability space `(Ω, P)`, every
random run `ω ↦ run ω` of the sequential first-price auction and every (random) tie rule `win`
of the benchmark: if for every player `i` the event "player `i` does not have competitive ratio at
most `γ` and regret at most `Reg`" has probability at most `δ`, then the event
`LW < (LW* − C·n·(Reg + 1))/(γ + 1/2 + K/γ)` has probability at most `n·δ`.

**Formalization Note** `O(n)` and `O(1/γ)` are `C·n` and `K/γ` with `C, K` chosen before every other
quantity. Probabilities are those of Mathlib's measure on arbitrary sets (outer measure); no
measurability or independence is assumed. Values, bids, the winner and the tie rule may all
depend on `ω`; budgets are fixed. `Reg ≥ −1` corrects the printed statement, which is false for
`Reg < −1`. -/
theorem theorem_4_2 :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ (n T : ℕ) (γ Reg δ : ℝ), 1 ≤ γ → -1 ≤ Reg → 0 ≤ δ →
      ∀ (B : Fin n → ℝ), (∀ i, 0 ≤ B i) →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω),
        MeasureTheory.IsProbabilityMeasure P →
      ∀ (run : Ω → Outcome n T) (win : Ω → Fin n → Fin T → ℝ → Prop),
        (∀ ω, IsTieRule (run ω) (win ω)) →
        (∀ i : Fin n, P {ω | ¬ CR B (run ω) (win ω) γ Reg i} ≤ ENNReal.ofReal δ) →
        P {ω | LW B (run ω) < (LWstar B (run ω) - C * n * (Reg + 1)) / (γ + 1 / 2 + K / γ)}
          ≤ ENNReal.ofReal (n * δ) := by sorry

end LiquidWelfareFPA
