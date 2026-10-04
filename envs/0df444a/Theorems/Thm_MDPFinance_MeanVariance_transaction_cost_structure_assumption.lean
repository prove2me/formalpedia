-- Prove2me | Theorems.Thm_MDPFinance_MeanVariance_transaction_cost_structure_assumption
-- name    : MDPFinance.MeanVariance.transaction_cost_structure_assumption
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:08:28.387338+00:00
-- url     : https://prove2.me/theorems/b7229f7a-aad7-4a3d-81ee-9e2c3ed7e049
-- title:
--   Proposition 4.5.2 — the Structure Assumption (SAN) via buy/hold/sell decision rules
-- statement:
--   The Structure Assumption (SAN) of Theorem 2.3.8 holds for the transaction-cost model with
--   $\mathbb{M}_n := \mathbb{M}$ and $\Delta_n := \Delta\cap F_n$, where $\Delta$ is the class of
--   buy/hold/sell decision rules (Eq. (4.26)): $g_N\in\mathbb{M}$; $v\in\mathbb{M}\Rightarrow
--   T_nv\in\mathbb{M}$; and every $v\in\mathbb{M}$ admits a maximizer of $T_nv$ that is itself a
--   buy/hold/sell rule.
--
--   This is the structural fact underlying Theorem 4.5.4's explicit solution: because the maximizer
--   of the one-period problem is always of buy/hold/sell form, the optimal policy at *every* horizon
--   is a buy/hold/sell rule, with the two thresholds $q^-,q^+$ read off the next value function.
--
--   **Formalization Note.** The existence-of-maximizer clause packages "some buy/hold/sell $f$
--   attains the supremum defining $T_nv$" rather than restating the book's constructive derivation of
--   $f^*$'s threshold $q^+$ from the state $(0,1)$ (the proof's Eq. (4.27)-(4.28)); that derivation is
--   proof content, not part of the numbered statement.
--
--   **Formalization Note (moderation).** The maximizer clause is stated on $E$ with the corrected
--   $\mathbb{M}$ (including the $\mathbb{B}_b^+$ bound, without which $T_n v$ need not be defined).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 109, PDF 123, Proposition 4.5.2

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_TransactionCostMarket
import Definitions.Def_MDPFinance_MeanVariance_TransactionCostOperators

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- Proposition 4.5.2 (Bäuerle–Rieder, p. 109, PDF 123). The Structure Assumption (SAN) is
satisfied for the transaction-cost model with `IM_n := IM` and `Δ_n := Δ ∩ F_n`: `g_N ∈ IM`;
`v ∈ IM ⟹ T_n v ∈ IM`; every `v ∈ IM` has a maximizer that is a buy/hold/sell decision rule
(4.26). -/
theorem transaction_cost_structure_assumption {Ω : Type*} [MeasurableSpace Ω]
    (M : TransactionCostMarket Ω) :
    IsInIM M.γ (fun x => M.U (x.1 + x.2)) ∧
      (∀ n < M.N, ∀ v : ℝ × ℝ → ℝ, IsInIM M.γ v → IsInIM M.γ (fun x => M.T n v x.1 x.2)) ∧
      (∀ n < M.N, ∀ v : ℝ × ℝ → ℝ, IsInIM M.γ v →
        ∃ f : ℝ × ℝ → ℝ, IsBuyHoldSellRule f ∧ Measurable f ∧
          ∀ x ∈ Estate, f x ∈ M.Arange x.1 x.2 ∧
            ∫ ω, v (M.h x.1 x.2 (f x) * (1 + M.i (n + 1)),
              f x * M.Rtilde (n + 1) ω) ∂M.measIP = M.T n v x.1 x.2) := by sorry

end MDPFinance.MeanVariance
