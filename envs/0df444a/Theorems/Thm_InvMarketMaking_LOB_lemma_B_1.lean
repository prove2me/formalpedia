-- Prove2me | Theorems.Thm_InvMarketMaking_LOB_lemma_B_1
-- name    : InvMarketMaking.LOB.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:22:23.304672+00:00
-- url     : https://prove2.me/theorems/721419e5-9f9d-41a6-9a99-6e0de54b5673
-- title:
--   Lemma B.1 — on the good event, $F^{\mathrm{low}}_t\le F\le F^{\mathrm{up}}_t$ within $2\psi_t$ (and likewise for $S$) on active prices
-- statement:
--   Run Algorithm 4 on finite grids $\mathcal B^\circ,\mathcal A^\circ\subset[0,1]$ with radii $\psi_t$, and let $F^{\mathrm{up}}_t,F^{\mathrm{low}}_t,S^{\mathrm{up}}_t,S^{\mathrm{low}}_t$ be its confidence bounds (20)–(21) after round $t$, built from its limit-order-book estimates, with $\psi_0=1$. On the good event (16) up to $T$, for every $t\le T$ and every active pair $b\in\mathcal B^\circ_t$, $a\in\mathcal A^\circ_t$:
--   $$
--   F(b)-2\psi_t(b)\le F^{\mathrm{low}}_t(b)\le F(b)\le F^{\mathrm{up}}_t(b)\le F(b)+2\psi_t(b),
--   $$
--   $$
--   S(a)-2\psi_t(a)\le S^{\mathrm{low}}_t(a)\le S(a)\le S^{\mathrm{up}}_t(a)\le S(a)+2\psi_t(a).
--   $$
--   The bounds of the algorithm are therefore valid and at most twice the radius away from the truth on every price still in play.
--
--   Differences from the source:
--   - generalization: any time t ∈ [T] → any t ∈ {0, 1, …, T}; reason: at t = 0 the estimates are 0 and ψ_0 = 1 (Line 2), so the bounds are [0, 1] and the claim holds; Algorithm 4 uses the bound at time t − 1 in round t
--   - reading: every active (b, a) pair at time t → b ∈ B°_t and a ∈ A°_t, the active sets of Algorithm 4 after round t (Lines 5–6); reason: these are the sets on which Algorithm 4 uses its bounds
--   - generalization: radii ψ_t such that (16) holds with probability at least 1 − δ (Notation 6.9) → arbitrary real-valued radii; reason: the conclusion is asserted on the good event and uses no property of the radii; the paper's radii are instances
--   - reading: Algorithm 5 has no return statement after its second loop (Line 26) → it then returns the outer pair (b_0, a_{M−1}); reason: the paper leaves this case undefined; the outer pair keeps the active sets nested, and on grids with a pair b < a and nonnegative radii it is never reached (Proposition 6.11)
--   - reading: Line 23 of Algorithm 4 updates F̂_t, Ŝ_t on the active sets only → F̂_t(b) = (1/t) Σ_{τ≤t} χ^sell_τ(b) and Ŝ_t(a) = (1/t) Σ_{τ≤t} χ^buy_τ(a) for every price, with F̂_0 = Ŝ_0 = 0; reason: Algorithm 5 evaluates the bounds only on the active sets, which are nested, so the values the algorithm uses are the same
--   - reading: S(a) = E[I(V^buy ≥ a)] = 1 − F_buy(a) (p. 16) → S(a) = P(V^buy ≥ a); reason: the two expressions differ exactly at atoms of V^buy; the trade probability E[I(V^buy ≥ a)] is what the model and every proof use (p. 59 also writes S(a) = P(−V^buy ≤ −a))
--   - generalization: rounds whose valuation pairs are i.i.d. from the valuation law V of Sec. 3 (supported in [0, 1]², P(V^buy = 1) = P(V^sell = 0) = 0) → any probability law V on ℝ² and arbitrary real valuation and draw sequences (no probability model); reason: the claim is pathwise on the good event and uses only that F and S take values in [0, 1]; the paper's model is an instance
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Lemma B.1, p. 59

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_J
import Definitions.Def_InvMarketMaking_LOB_lobRound
import Definitions.Def_InvMarketMaking_LOB_goodEvent

open MeasureTheory ProbabilityTheory

namespace InvMarketMaking.LOB

/-- **Lemma B.1** (Maran, Restelli, Stradi, arXiv:2610.24562v1, p. 59). Under the good event (16),
for every active pair `(b, a)` (`b ∈ B°_t`, `a ∈ A°_t`) at any time `t`:
`F(b) − 2ψ_t(b) ≤ F^low_t(b) ≤ F(b) ≤ F^up_t(b) ≤ F(b) + 2ψ_t(b)` and
`S(a) − 2ψ_t(a) ≤ S^low_t(a) ≤ S(a) ≤ S^up_t(a) ≤ S(a) + 2ψ_t(a)`.

**Formalization Note** `F^up_t, F^low_t, S^up_t, S^low_t` are Algorithm 4's bounds (20)–(21), built
from its observable estimates (17); `B°_t, A°_t` are its active sets after round `t`. Stated for
every outcome of the good event and every `t ≤ T`, including `t = 0` (where `ψ_0 = 1` and the
bounds are `[0,1]`). The grids are subsets of `[0,1]`; the radii are arbitrary. -/
theorem lemma_B_1 {Ω : Type*} (V : Measure (ℝ × ℝ)) [IsProbabilityMeasure V] (C : LOBConfig Ω)
    (M : Market Ω) (hB : ↑C.Bg ⊆ Set.Icc (0 : ℝ) 1) (hA : ↑C.Ag ⊆ Set.Icc (0 : ℝ) 1)
    (T : ℕ) (ω : Ω) (hω : ω ∈ goodEvent V C M T) (t : ℕ) (ht : t ≤ T)
    (b : ℝ) (hb : b ∈ (lobRound C M t ω).activeB) (a : ℝ) (ha : a ∈ (lobRound C M t ω).activeA) :
    (sellCdf V b - 2 * radF C t b ω ≤ Flo C M t b ω ∧ Flo C M t b ω ≤ sellCdf V b ∧
      sellCdf V b ≤ Fup C M t b ω ∧ Fup C M t b ω ≤ sellCdf V b + 2 * radF C t b ω) ∧
    (buySurv V a - 2 * radS C t a ω ≤ Slo C M t a ω ∧ Slo C M t a ω ≤ buySurv V a ∧
      buySurv V a ≤ Sup C M t a ω ∧ Sup C M t a ω ≤ buySurv V a + 2 * radS C t a ω) := by sorry

end InvMarketMaking.LOB
