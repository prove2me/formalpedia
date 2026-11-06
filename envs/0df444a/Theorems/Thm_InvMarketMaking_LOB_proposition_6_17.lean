-- Prove2me | Theorems.Thm_InvMarketMaking_LOB_proposition_6_17
-- name    : InvMarketMaking.LOB.proposition_6_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:20:35.066197+00:00
-- url     : https://prove2.me/theorems/e78da108-aa35-43c6-94a2-eaa551461312
-- title:
--   Proposition 6.17 — on the grid (22), $R^J_t\le R^\circ_t+2t/N$
-- statement:
--   Let $N\ge1$, let the bid and ask grids be $\mathcal B^\circ=\mathcal A^\circ=\{n/N:n=0,\dots,N\}$ (Eq. (22)), and let $(b^\circ,a^\circ)$ be any maximizer of $J$ on them. For any algorithm, that is, for any sequence of rewards $r_1,r_2,\dots$, and every $t$,
--   $$
--   R^J_t\le R^\circ_t+2\,\frac tN,
--   $$
--   where $R^J_t=tJ^*-\sum_{\tau\le t}r_\tau$ is the surrogate regret and $R^\circ_t=tJ(b^\circ,a^\circ)-\sum_{\tau\le t}r_\tau$ the virtual regret.
--
--   Differences from the source:
--   - generalization: any algorithm working on the discretized sets of (22), at every t ≤ T, for the valuation laws of Sec. 3 → any real reward sequence, every t ∈ ℕ, any probability law V on ℝ²; reason: the inequality involves the rewards only through the common sum, and the grid bound (Proposition 4.3) holds for every probability law
--   - reading: R^J_T (Eq. (5)) and R°_T (Definition 4.5) at the horizon → R^J_t = t·J* − Σ_{τ≤t} r_τ and R°_t = t·J(b°, a°) − Σ_{τ≤t} r_τ at every t; reason: the 2(t/N) term and the phrase 'at every t ≤ T' fix this normalization
--   - reading: the pair (b°, a°) of Definition 4.4 → every maximizer of J on B° × A°; reason: p. 19: all results hold regardless of how ties are broken
--   - reading: S(a) = E[I(V^buy ≥ a)] = 1 − F_buy(a) (p. 16) → S(a) = P(V^buy ≥ a); reason: the two expressions differ exactly at atoms of V^buy; the trade probability E[I(V^buy ≥ a)] is what the model and every proof use (p. 59 also writes S(a) = P(−V^buy ≤ −a))
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Proposition 6.17, p. 47

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_J
import Definitions.Def_InvMarketMaking_LOB_grid
import Definitions.Def_InvMarketMaking_LOB_IsGridOpt
import Definitions.Def_InvMarketMaking_LOB_surrogateRegret

open MeasureTheory ProbabilityTheory

namespace InvMarketMaking.LOB

/-- **Proposition 6.17** (Maran, Restelli, Stradi, arXiv:2610.24562v1, p. 47). For any algorithm
working on the discretized sets `B° = A° = {n/N : n = 0, …, N}` of Eq. (22), at every `t ≤ T`,
`R^J_t ≤ R°_t + 2(t/N)`.

**Formalization Note** "Any algorithm" is an arbitrary real reward sequence `r`; `R^J_t` and
`R°_t` are the surrogate regret (5) and the virtual regret (Definition 4.5) at time `t`, against any
maximizer `(b°, a°)` of `J` on the grid. `N ≥ 1`; the inequality holds for every `t`. -/
theorem proposition_6_17 (V : Measure (ℝ × ℝ)) [IsProbabilityMeasure V] (N : ℕ) (hN : 0 < N)
    (bo ao : ℝ) (hopt : IsGridOpt V (grid N) (grid N) bo ao) (r : ℕ → ℝ) (t : ℕ) :
    surrogateRegret V r t ≤ virtualRegret V bo ao r t + 2 * ((t : ℝ) / N) := by sorry

end InvMarketMaking.LOB
