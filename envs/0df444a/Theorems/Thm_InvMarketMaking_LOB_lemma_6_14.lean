-- Prove2me | Theorems.Thm_InvMarketMaking_LOB_lemma_6_14
-- name    : InvMarketMaking.LOB.lemma_6_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:22:50.381202+00:00
-- url     : https://prove2.me/theorems/0013e161-70e4-4172-9c21-f20c149c2ab7
-- title:
--   Lemma 6.14 — on the good event $J^{\mathrm{low}}_t\le J\le J^{\mathrm{up}}_t$ on active pairs $b<a$
-- statement:
--   Run Algorithm 4 on finite grids $\mathcal B^\circ,\mathcal A^\circ\subset[0,1]$ with radii $\psi_t$ ($\psi_0=1$) and let
--   $$
--   J^{\mathrm{up}}_t(b,a)=(a-b)\min\{F^{\mathrm{up}}_t(b),S^{\mathrm{up}}_t(a)\},\qquad J^{\mathrm{low}}_t(b,a)=(a-b)\min\{F^{\mathrm{low}}_t(b),S^{\mathrm{low}}_t(a)\}.
--   $$
--   On the good event (16) up to $T$, for every $t\le T$ and every pair $b\in\mathcal B^\circ_t$, $a\in\mathcal A^\circ_t$ with $b<a$,
--   $$
--   J^{\mathrm{low}}_t(b,a)\le J(b,a)\le J^{\mathrm{up}}_t(b,a).
--   $$
--   This is what makes the elimination rule of Algorithm 5 safe.
--
--   Differences from the source:
--   - generalization: any time t ∈ [T] → any t ∈ {0, 1, …, T}; reason: at t = 0 the estimates are 0 and ψ_0 = 1 (Line 2), so the bounds are [0, 1] and the claim holds; Algorithm 4 uses the bound at time t − 1 in round t
--   - generalization: radii ψ_t such that (16) holds with probability at least 1 − δ (Notation 6.9) → arbitrary real-valued radii; reason: the conclusion is asserted on the good event and uses no property of the radii; the paper's radii are instances
--   - reading: Algorithm 5 has no return statement after its second loop (Line 26) → it then returns the outer pair (b_0, a_{M−1}); reason: the paper leaves this case undefined; the outer pair keeps the active sets nested, and on grids with a pair b < a and nonnegative radii it is never reached (Proposition 6.11)
--   - reading: Line 23 of Algorithm 4 updates F̂_t, Ŝ_t on the active sets only → F̂_t(b) = (1/t) Σ_{τ≤t} χ^sell_τ(b) and Ŝ_t(a) = (1/t) Σ_{τ≤t} χ^buy_τ(a) for every price, with F̂_0 = Ŝ_0 = 0; reason: Algorithm 5 evaluates the bounds only on the active sets, which are nested, so the values the algorithm uses are the same
--   - reading: S(a) = E[I(V^buy ≥ a)] = 1 − F_buy(a) (p. 16) → S(a) = P(V^buy ≥ a); reason: the two expressions differ exactly at atoms of V^buy; the trade probability E[I(V^buy ≥ a)] is what the model and every proof use (p. 59 also writes S(a) = P(−V^buy ≤ −a))
--   - generalization: rounds whose valuation pairs are i.i.d. from the valuation law V of Sec. 3 (supported in [0, 1]², P(V^buy = 1) = P(V^sell = 0) = 0) → any probability law V on ℝ² and arbitrary real valuation and draw sequences (no probability model); reason: the claim is pathwise on the good event and uses only that F and S take values in [0, 1]; the paper's model is an instance
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Lemma 6.14, p. 44

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_J
import Definitions.Def_InvMarketMaking_LOB_lobRound
import Definitions.Def_InvMarketMaking_LOB_goodEvent

open MeasureTheory ProbabilityTheory

namespace InvMarketMaking.LOB

/-- **Lemma 6.14** (Maran, Restelli, Stradi, arXiv:2610.24562v1, p. 44). With
`J^up_t(b, a) = (a − b) min{F^up_t(b), S^up_t(a)}` and `J^low_t(b, a) = (a − b) min{F^low_t(b), S^low_t(a)}`,
under the good event, for every pair `b ∈ B°_t`, `a ∈ A°_t` with `b < a`:
`J^low_t(b, a) ≤ J(b, a) ≤ J^up_t(b, a)`.

**Formalization Note** Stated for Algorithm 4 with grids in `[0,1]` and arbitrary radii, for every
outcome of the good event and every `t ≤ T`, including `t = 0` (Algorithm 4 uses the lemma at time
`t − 1` in round `t`). -/
theorem lemma_6_14 {Ω : Type*} (V : Measure (ℝ × ℝ)) [IsProbabilityMeasure V] (C : LOBConfig Ω)
    (M : Market Ω) (hB : ↑C.Bg ⊆ Set.Icc (0 : ℝ) 1) (hA : ↑C.Ag ⊆ Set.Icc (0 : ℝ) 1)
    (T : ℕ) (ω : Ω) (hω : ω ∈ goodEvent V C M T) (t : ℕ) (ht : t ≤ T)
    (b : ℝ) (hb : b ∈ (lobRound C M t ω).activeB) (a : ℝ) (ha : a ∈ (lobRound C M t ω).activeA)
    (hba : b < a) :
    Jlow C M t b a ω ≤ J V b a ∧ J V b a ≤ Jup C M t b a ω := by sorry

end InvMarketMaking.LOB
