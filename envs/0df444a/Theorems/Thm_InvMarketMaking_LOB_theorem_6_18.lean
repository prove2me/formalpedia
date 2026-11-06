-- Prove2me | Theorems.Thm_InvMarketMaking_LOB_theorem_6_18
-- name    : InvMarketMaking.LOB.theorem_6_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:22:31.38723+00:00
-- url     : https://prove2.me/theorems/7b564e85-efa1-48b2-8abc-fd50620ca5c4
-- title:
--   Theorem 6.18 — with LOB feedback, w.p. $1-\delta$: $|I_t|\le 10\sqrt{T\log(12T/\delta)}$ and $R^J_t\le 15\sqrt{T\log(12T/\delta)}$ for all $t\le T$
-- statement:
--   A market maker faces, in each round $t=1,\dots,T$, a fresh seller and buyer whose valuations $(V^{\mathrm{sell}}_t,V^{\mathrm{buy}}_t)$ are i.i.d. draws from an unknown joint law $\mathcal V$ on $[0,1]^2$ with $\mathbb P(V^{\mathrm{buy}}=1)=\mathbb P(V^{\mathrm{sell}}=0)=0$; the two valuations of a round may be arbitrarily correlated. It posts a bid $B_t$ and an ask $A_t$, buys if $V^{\mathrm{sell}}_t\le B_t$, sells if $V^{\mathrm{buy}}_t\ge A_t$, and observes limit-order-book feedback. Its reward is $r_t=A_t\mathbb I(V^{\mathrm{buy}}_t\ge A_t)-B_t\mathbb I(V^{\mathrm{sell}}_t\le B_t)$ and its imbalance $I_t=\sum_{\tau\le t}\mathbb I(V^{\mathrm{sell}}_\tau\le B_\tau)-\sum_{\tau\le t}\mathbb I(V^{\mathrm{buy}}_\tau\ge A_\tau)$. With $J(b,a)=(a-b)\min\{F(b),S(a)\}$ and $J^*=\sup_{[0,1]^2}J$, the surrogate regret is $R^J_t=tJ^*-\sum_{\tau\le t}r_\tau$.
--
--   Let $T\ge1$ and $\delta\in(0,1)$. Run Algorithm 4 with $\psi_0=1$, $\psi_t(b,\delta)=\psi_t(a,\delta)=\min\{1,\sqrt{\log(12T/\delta)/(2t)}\}$, and the grids $\mathcal B^\circ=\mathcal A^\circ=\{n/N:n=0,\dots,N\}$ of Eq. (22) with $N=\lceil\sqrt T\rceil$. Then, with probability at least $1-\delta$, simultaneously for all $t\in\{1,\dots,T\}$,
--   $$
--   |I_t|\le10\sqrt{T\log(12T/\delta)},\qquad R^J_t\le15\sqrt{T\log(12T/\delta)}.
--   $$
--   Both the inventory and the regret against the surrogate benchmark grow as $\widetilde O(\sqrt T)$, uniformly over time, for every valuation law satisfying the standing assumptions.
--
--   Differences from the source:
--   - reading: with probability at least 1 − δ simultaneously for all the t time-steps → P(∀ t ∈ {1, …, T}: both bounds) ≥ 1 − δ; reason: one event carries all t; the quantifier is inside the probability
--   - reading: R^J_T (Eq. (5)) at the horizon → R^J_t = t·J* − Σ_{τ≤t} r_τ at every t; reason: Theorem 6.18 bounds R^J_t at every t, and Proposition 6.17's 2(t/N) fixes the t·J* normalization
--   - encoding: T rounds with (V^sell_t, V^buy_t) i.i.d. from V and the Bernoulli draws X ∼ Bern(p), Y ∼ Bern(p) of Algorithm 4 → measurable sequences indexed by ℕ whose round vectors ((V^sell_t, V^buy_t), U_t) are mutually independent with law V ⊗ Unif[0,1]; a draw Bern(p) is 1{U_t < p}; index 0 and indices beyond T are unused; reason: given the past, 1{U_t < p} has law Bern(p); at most one draw is made per round; every event involves rounds 1, …, T only
--   - encoding: Algorithm 5 has no return statement after its second loop (Line 26) → it then returns the outer pair (b_0, a_{M−1}); reason: under this statement's hypotheses (a grid pair b < a, nonnegative radii) the loop always returns (Proposition 6.11), so the fallback is never used
--   - reading: Line 23 of Algorithm 4 updates F̂_t, Ŝ_t on the active sets only → F̂_t(b) = (1/t) Σ_{τ≤t} χ^sell_τ(b) and Ŝ_t(a) = (1/t) Σ_{τ≤t} χ^buy_τ(a) for every price, with F̂_0 = Ŝ_0 = 0; reason: Algorithm 5 evaluates the bounds only on the active sets, which are nested, so the values the algorithm uses are the same
--   - encoding: log → Real.log, the natural logarithm; reason: the DKW and Azuma exponents are base e
--   - reading: S(a) = E[I(V^buy ≥ a)] = 1 − F_buy(a) (p. 16) → S(a) = P(V^buy ≥ a); reason: the two expressions differ exactly at atoms of V^buy; the trade probability E[I(V^buy ≥ a)] is what the model and every proof use (p. 59 also writes S(a) = P(−V^buy ≤ −a))
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Theorem 6.18, p. 47

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_IsValuationLaw
import Definitions.Def_InvMarketMaking_LOB_J
import Definitions.Def_InvMarketMaking_LOB_IsRoundModel
import Definitions.Def_InvMarketMaking_LOB_lobRound
import Definitions.Def_InvMarketMaking_LOB_surrogateRegret
import Definitions.Def_InvMarketMaking_LOB_dkwConfig

open MeasureTheory ProbabilityTheory

namespace InvMarketMaking.LOB

/-- **Theorem 6.18** (Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market
Making Under Inventory Constraints, arXiv:2610.24562v1, p. 47). Let `δ ∈ (0, 1)`. Use `ψ_0 = 1`,
`ψ_t(b, δ) = ψ_t(a, δ) = min{1, √(log(12T/δ)/(2t))}` and `N = ⌈√T⌉` in Eq. (22). Then Algorithm 4
enjoys, with probability at least `1 − δ` simultaneously for all the time-steps `t ∈ [T]`,
`|I_t| ≤ 10 √(T log(12T/δ))` and `R^J_t ≤ 15 √(T log(12T/δ))`.

**Formalization Note** The valuation pairs are i.i.d. from any joint law `V` on `[0,1]²` with
`P(V^buy = 1) = P(V^sell = 0) = 0` (Sec. 3, p. 14), the two coordinates arbitrarily correlated;
the algorithm's Bernoulli draws are `1{U_t < p}` with `U_t` uniform and independent
(`IsRoundModel`). The algorithm uses limit-order-book feedback only (its estimates are those of
Eq. (17)). `R^J_t = t·J* − Σ_{τ ≤ t} r_τ` with `J*` the supremum of `J` over `[0,1]²`. The quantifier
over `t` is inside the event. `T ≥ 1`; `log` is the natural logarithm. -/
theorem theorem_6_18 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Measure (ℝ × ℝ)) [IsProbabilityMeasure V] (hV : IsValuationLaw V)
    (M : Market Ω) (hM : IsRoundModel P V M)
    (T : ℕ) (hT : 1 ≤ T) (δ : ℝ) (hδ : δ ∈ Set.Ioo 0 1) :
    ENNReal.ofReal (1 - δ) ≤ P {ω | ∀ t ∈ Finset.Icc 1 T,
      |imbalance (dkwConfig Ω T δ) M t ω| ≤ 10 * Real.sqrt (T * Real.log (12 * T / δ)) ∧
      surrogateRegret V (fun τ => reward (dkwConfig Ω T δ) M τ ω) t ≤
        15 * Real.sqrt (T * Real.log (12 * T / δ))} := by sorry

end InvMarketMaking.LOB
