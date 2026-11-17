-- Prove2me | Theorems.Thm_InvMarketMaking_LOB_Supplement_theorem_5_13
-- name    : InvMarketMaking.LOB.Supplement.theorem_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:33:14.83423+00:00
-- url     : https://prove2.me/theorems/1a0620e1-0844-4417-9367-f32ac547ae4a
-- title:
--   Theorem 5.13 — two-bit feedback: w.p. $1-\delta$, $|I_t|\le 59T^{2/3}\sqrt{\log(4T/\delta)}$ and $R^J_t\le 109T^{2/3}\sqrt{\log(4T/\delta)}$ for all $t\le T$
-- statement:
--   In each round $t=1,\dots,T$ a fresh seller and buyer arrive with valuations $(V^{\mathrm{sell}}_t,V^{\mathrm{buy}}_t)$, i.i.d. across rounds from an unknown joint law $\mathcal V$ on $[0,1]^2$ with $\mathbb P(V^{\mathrm{buy}}=1)=\mathbb P(V^{\mathrm{sell}}=0)=0$. The two valuations of a round may be correlated. The maker posts $(B_t,A_t)$ and receives $r_t=A_t\mathbb I(V^{\mathrm{buy}}_t\ge A_t)-B_t\mathbb I(V^{\mathrm{sell}}_t\le B_t)$. Its imbalance is $I_t=\sum_{\tau\le t}\mathbb I(V^{\mathrm{sell}}_\tau\le B_\tau)-\sum_{\tau\le t}\mathbb I(V^{\mathrm{buy}}_\tau\ge A_\tau)$. With $J(b,a)=(a-b)\min\{F(b),S(a)\}$ and $J^*=\sup_{[0,1]^2}J$, the surrogate regret is $R^J_t=tJ^*-\sum_{\tau\le t}r_\tau$.
--
--   Let $T\ge1$ and $\delta\in(0,1)$, and run Algorithm 1, which observes only the two trade bits. Then for every argmax tie-break rule, with probability at least $1-\delta$, simultaneously for all $t\in\{1,\dots,T\}$,
--   $$
--   |I_t|\le 59\,T^{2/3}\sqrt{\log(4T/\delta)},\qquad R^J_t\le 109\,T^{2/3}\sqrt{\log(4T/\delta)}.
--   $$
--   With two-bit feedback, both the inventory excursion and the surrogate regret are $\widetilde O(T^{2/3})$, uniformly over time and over valuation laws.
--
--   Differences from the source:
--   - reading: with probability at least 1 − δ, simultaneously over all the t time-steps → P(∀ t ∈ {1, …, T}: both bounds) ≥ 1 − δ; reason: one event carries all t; the quantifier is inside the probability
--   - reading: R^J_T (Eq. (5)) at the horizon → R^J_t = t·J* − Σ_{τ≤t} r_τ at every t ∈ [T] (the published surrogateRegret); reason: the theorem bounds R^J_t at every t; the proof (p. 32) works with t·J*
--   - encoding: T rounds with (V^sell_t, V^buy_t) i.i.d. from V → measurable sequences indexed by ℕ, mutually independent, each with law V (IsValuationModel); index 0 and indices beyond T unused; reason: every event involves rounds 1, …, T only
--   - reading: a′ ← argmax{S^up_ℓ(a) : a ∈ C_ℓ(b)}, b′ ← argmax{F^up_ℓ(b) : b ∈ C_ℓ(a)}, no tie-break → an arbitrary argmax selection rule sel, quantified universally (IsArgmaxRule sel); reason: the page leaves ties open; the universal statement covers every tie-break
--   - reading: 'for b ∈ B_ℓ do … for a ∈ A_ℓ do' (Lines 7–13), order within each set unspecified → bid calls in increasing price order, then ask calls in increasing price order; reason: the page fixes bids before asks but no order within a set; every call uses only phase-ℓ quantities, so the order changes only which rounds a call occupies
--   - reading: no rule when no price remains active (B_ℓ = ∅) → Algorithm 1 posts (0, 1) from then on, as in footnote 4's fallback; reason: no call can be made; (0, 1) is the no-trade pair the paper uses for every fallback; on the good event (b°, a°) stays active
--   - encoding: log → Real.log, the natural logarithm; reason: the concentration exponents are base e
--   - reading: S(a) = E[I(V^buy ≥ a)] = 1 − F_buy(a) (p. 16) → S(a) = P(V^buy ≥ a) (the published buySurv); reason: the two expressions differ exactly at atoms of V^buy; the trade probability E[I(V^buy ≥ a)] is what Program (3), the model and every proof use; Eq. (24) is also P(V^buy ≥ a)
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Theorem 5.13, p. 31

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_IsValuationLaw
import Definitions.Def_InvMarketMaking_LOB_J
import Definitions.Def_InvMarketMaking_LOB_surrogateRegret
import Definitions.Def_InvMarketMaking_LOB_Supplement_ppImbalance
import Definitions.Def_InvMarketMaking_LOB_Supplement_twoBitMaker

open MeasureTheory ProbabilityTheory

namespace InvMarketMaking.LOB.Supplement

/-- **Theorem 5.13** (Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market
Making Under Inventory Constraints, arXiv:2610.24562v1, p. 31). Let `δ ∈ (0, 1)`. Then Algorithm 1
enjoys, with probability at least `1 − δ`, simultaneously over all the time-steps `t ∈ [T]`,
`|I_t| ≤ 59 T^{2/3} √(log(4T/δ))` and `R^J_t ≤ 109 T^{2/3} √(log(4T/δ))`.

**Formalization Note** The valuation pairs are i.i.d. from any joint law `V` on `[0,1]²` with
`P(V^buy = 1) = P(V^sell = 0) = 0` (Sec. 3, p. 14), arbitrarily correlated within a round. Algorithm 1
is `twoBitMaker` with grids `B° = {n/⌊T^{1/3}⌋ : 0 ≤ n < ⌊T^{1/3}⌋}`, `A° = {n/⌊T^{1/3}⌋ : 1 ≤ n ≤ ⌊T^{1/3}⌋}`;
the bound holds for every argmax tie-break rule. `R^J_t = t·J* − Σ_{τ ≤ t} r_τ`. The quantifier over
`t` is inside the event. `T ≥ 1`; `log` is the natural logarithm; `T^{2/3}` is the real power. -/
theorem theorem_5_13 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Measure (ℝ × ℝ)) [IsProbabilityMeasure V] (hV : IsValuationLaw V)
    (M : Market Ω) (hM : IsValuationModel P V M)
    (T : ℕ) (hT : 1 ≤ T) (δ : ℝ) (hδ : δ ∈ Set.Ioo 0 1)
    (sel : Finset ℝ → (ℝ → ℝ) → ℝ) (hsel : IsArgmaxRule sel) :
    ENNReal.ofReal (1 - δ) ≤ P {ω | ∀ t ∈ Finset.Icc 1 T,
      |ppImbalance M (twoBitBid T δ sel M) (twoBitAsk T δ sel M) t ω| ≤
        59 * (T : ℝ) ^ ((2 : ℝ) / 3) * Real.sqrt (Real.log (4 * T / δ)) ∧
      surrogateRegret V (fun τ => ppReward M (twoBitBid T δ sel M) (twoBitAsk T δ sel M) τ ω) t ≤
        109 * (T : ℝ) ^ ((2 : ℝ) / 3) * Real.sqrt (Real.log (4 * T / δ))} := by sorry

end InvMarketMaking.LOB.Supplement
