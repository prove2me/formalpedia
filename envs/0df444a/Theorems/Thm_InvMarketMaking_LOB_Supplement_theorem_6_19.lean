-- Prove2me | Theorems.Thm_InvMarketMaking_LOB_Supplement_theorem_6_19
-- name    : InvMarketMaking.LOB.Supplement.theorem_6_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:34:50.4018+00:00
-- url     : https://prove2.me/theorems/cc13a131-0b58-428e-b1ff-d468214bb8eb
-- title:
--   Theorem 6.19 — instance-dependent LOB bound: $|I_t|,R^J_t\lesssim\sqrt{\max\{F(b^\circ),S(a^\circ)\}T\log(12T/\delta)}+(1+\log T)\log(12T/\delta)$
-- statement:
--   In the model of Theorem 6.18, the valuation pairs $(V^{\mathrm{sell}}_t,V^{\mathrm{buy}}_t)$ are i.i.d. from a joint law $\mathcal V$ on $[0,1]^2$ with $\mathbb P(V^{\mathrm{buy}}=1)=\mathbb P(V^{\mathrm{sell}}=0)=0$, and the maker has limit-order-book feedback. Let $T\ge1$ and $\delta\in(0,1)$. Run Algorithm 4 with $\psi_0=1$, the grids $\mathcal B^\circ=\mathcal A^\circ=\{n/T:n=0,\dots,T\}$ of Eq. (22) with $N=T$, and the empirical-Bernstein radii of Proposition 6.5 with failure parameter $\delta/6$. Let $(b^\circ,a^\circ)$ be any maximizer of $J$ on $\mathcal B^\circ\times\mathcal A^\circ$. Then, with probability at least $1-\delta$, simultaneously for all $t\in\{1,\dots,T\}$,
--   $$
--   |I_t|\le 256\sqrt{\max\{F(b^\circ),S(a^\circ)\}\,T\log(12T/\delta)}+1728\,(1+\log T)\log(12T/\delta),
--   $$
--   $$
--   R^J_t\le 320\sqrt{\max\{F(b^\circ),S(a^\circ)\}\,T\log(12T/\delta)}+2160\,(1+\log T)\log(12T/\delta).
--   $$
--   When trades at the optimal grid pair are rare, both the inventory and the surrogate regret are much smaller than $\sqrt T$. Since $\max\{F(b^\circ),S(a^\circ)\}\le1$, the bound also implies the worst-case $\widetilde O(\sqrt T)$ rate.
--
--   Differences from the source:
--   - reading: with probability at least 1 − δ, simultaneously over all the t time-steps → P(∀ t ∈ {1, …, T}: both bounds) ≥ 1 − δ; reason: one event carries all t; the quantifier is inside the probability
--   - reading: R^J_T (Eq. (5)) at the horizon → R^J_t = t·J* − Σ_{τ≤t} r_τ at every t ∈ [T] (the published surrogateRegret); reason: the theorem bounds R^J_t at every t; the proof (p. 32) works with t·J*
--   - reading: the pair (b°, a°) of Definition 4.4, 'regardless of how ties are broken' (p. 19) → ∀ bo ao, IsGridOpt V (grid T) (grid T) bo ao → the probability bound; reason: the bound holds for every maximizer, the strongest reading
--   - reading: the radii of Proposition 6.5, built from F̂_t, Ŝ_t of Eq. (12), inside Algorithm 4, which has LOB feedback → the radius computed from the full-feedback empCdf/empSurv (ebConfig), fed to the published lobRound; reason: Algorithm 4 reads the radius only at active prices, where the full-feedback estimate equals its observable one (Proposition 6.7)
--   - encoding: T rounds with (V^sell_t, V^buy_t) i.i.d. from V and the Bernoulli draws of Algorithm 4 → the published IsRoundModel: round vectors ((V^sell_t, V^buy_t), U_t) mutually independent with law V ⊗ Unif[0,1]; Bern(p) = 1{U_t < p}; reason: as in the published Theorem 6.18; given the past, 1{U_t < p} has law Bern(p)
--   - encoding: Algorithm 5 has no return statement after its second loop (Line 26) → the published doublePointer then returns the outer pair (b_0, a_{M−1}); reason: as in the published Theorem 6.18; the grid {n/T} contains the pair 0 < 1
--   - reading: Line 23 of Algorithm 4 updates F̂_t, Ŝ_t on the active sets only → the published lobRound's observable estimates are defined at every price; reason: as in the published Theorem 6.18: the algorithm evaluates them only on the nested active sets
--   - encoding: log → Real.log, the natural logarithm; reason: the concentration exponents are base e
--   - reading: S(a) = E[I(V^buy ≥ a)] = 1 − F_buy(a) (p. 16) → S(a) = P(V^buy ≥ a) (the published buySurv); reason: the two expressions differ exactly at atoms of V^buy; the trade probability E[I(V^buy ≥ a)] is what Program (3), the model and every proof use; Eq. (24) is also P(V^buy ≥ a)
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Theorem 6.19, p. 48

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_IsValuationLaw
import Definitions.Def_InvMarketMaking_LOB_J
import Definitions.Def_InvMarketMaking_LOB_grid
import Definitions.Def_InvMarketMaking_LOB_IsGridOpt
import Definitions.Def_InvMarketMaking_LOB_IsRoundModel
import Definitions.Def_InvMarketMaking_LOB_lobRound
import Definitions.Def_InvMarketMaking_LOB_surrogateRegret
import Definitions.Def_InvMarketMaking_LOB_Supplement_ebConfig

open MeasureTheory ProbabilityTheory

namespace InvMarketMaking.LOB.Supplement

/-- **Theorem 6.19** (Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market
Making Under Inventory Constraints, arXiv:2610.24562v1, p. 48). Let `δ ∈ (0, 1)`. Use `ψ_0 = 1`, the two
radii in Proposition 6.5 with failure parameter `δ/6`, and `N = T` in Eq. (22). Then Algorithm 4
enjoys, with probability at least `1 − δ` simultaneously over all the time-steps `t ∈ [T]`,
`|I_t| ≤ 256 √(max{F(b°), S(a°)} T log(12T/δ)) + 1728 (1 + log T) log(12T/δ)` and
`R^J_t ≤ 320 √(max{F(b°), S(a°)} T log(12T/δ)) + 2160 (1 + log T) log(12T/δ)`.

**Formalization Note** The model is the one of Theorem 6.18 (`IsRoundModel`: i.i.d. valuation pairs
from any `V` satisfying the standing assumptions, arbitrarily correlated within a round, and the
uniform draws realizing the Bernoulli corrections of Algorithm 4). Algorithm 4 is the published
`lobRound` with the configuration `ebConfig M (grid T) (grid T) T (δ/6)`: grids
`B° = A° = {n/T : n = 0, …, T}` and the empirical-Bernstein radii at `δ/6`, i.e. with
`log(3(T+1)T/(δ/6))`; `ψ_0 = 1` is built into `lobRound`. `(b°, a°)` is any maximizer of `J` on the grid
(Definition 4.4), so the bound holds for every tie-break. The quantifier over `t` is inside the event.
`T ≥ 1`; `log` is the natural logarithm. -/
theorem theorem_6_19 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Measure (ℝ × ℝ)) [IsProbabilityMeasure V] (hV : IsValuationLaw V)
    (M : Market Ω) (hM : IsRoundModel P V M)
    (T : ℕ) (hT : 1 ≤ T) (δ : ℝ) (hδ : δ ∈ Set.Ioo 0 1) :
    ∀ bo ao : ℝ, IsGridOpt V (grid T) (grid T) bo ao →
      ENNReal.ofReal (1 - δ) ≤ P {ω | ∀ t ∈ Finset.Icc 1 T,
        |imbalance (ebConfig M (grid T) (grid T) T (δ / 6)) M t ω| ≤
          256 * Real.sqrt (max (sellCdf V bo) (buySurv V ao) * T * Real.log (12 * T / δ)) +
            1728 * (1 + Real.log T) * Real.log (12 * T / δ) ∧
        surrogateRegret V (fun τ => reward (ebConfig M (grid T) (grid T) T (δ / 6)) M τ ω) t ≤
          320 * Real.sqrt (max (sellCdf V bo) (buySurv V ao) * T * Real.log (12 * T / δ)) +
            2160 * (1 + Real.log T) * Real.log (12 * T / δ)} := by sorry

end InvMarketMaking.LOB.Supplement
