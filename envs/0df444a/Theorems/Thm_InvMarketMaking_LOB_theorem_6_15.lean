-- Prove2me | Theorems.Thm_InvMarketMaking_LOB_theorem_6_15
-- name    : InvMarketMaking.LOB.theorem_6_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:22:47.790579+00:00
-- url     : https://prove2.me/theorems/550b11f6-3f36-4e6e-b38f-4648cb461e82
-- title:
--   Theorem 6.15 — on the good event the virtual optimum $(b^\circ,a^\circ)$ is never eliminated
-- statement:
--   Run Algorithm 4 on finite grids $\mathcal B^\circ,\mathcal A^\circ\subset[0,1]$ containing a pair $b<a$, with nonnegative radii, and let $(b^\circ,a^\circ)$ be any maximizer of $J$ on $\mathcal B^\circ\times\mathcal A^\circ$ (Definition 4.4). On the good event (16) up to $T$, for every round $t\in\{1,\dots,T\}$,
--   $$
--   B_{t,0}\le b^\circ\qquad\text{and}\qquad a^\circ\le A_{t,0},
--   $$
--   that is, $b^\circ\in\mathcal B^\circ_t$ and $a^\circ\in\mathcal A^\circ_t$: the pair $b^\circ,a^\circ$ never gets eliminated.
--
--   Differences from the source:
--   - reading: the pair b°, a° never gets eliminated → for every round t ∈ [T], B_{t,0} ≤ b° and a° ≤ A_{t,0}; reason: the active sets are B° ∩ [B_{t,0}, 1] and A° ∩ [0, A_{t,0}] (Lines 5–6), so this is b° ∈ B°_t and a° ∈ A°_t
--   - reading: the pair (b°, a°) of Definition 4.4 → every maximizer of J on B° × A°; reason: p. 19: all results hold regardless of how ties are broken
--   - reading: arbitrary discretizations B°, A° of [0, 1] (Sec. 6.2) and radius functions of Notation 6.9 → finite grids in [0, 1] that contain a pair b < a, and nonnegative radii (any function of the outcome); reason: the model requires 0 ≤ B_t < A_t ≤ 1 (p. 14), which needs a grid pair b < a (see Proposition 6.11); every confidence radius is nonnegative
--   - generalization: radii ψ_t such that (16) holds with probability at least 1 − δ (Notation 6.9) → any nonnegative radii; reason: the conclusion is asserted on the good event; the paper's radii are instances
--   - encoding: Algorithm 5 has no return statement after its second loop (Line 26) → it then returns the outer pair (b_0, a_{M−1}); reason: under this statement's hypotheses (a grid pair b < a, nonnegative radii) the loop always returns (Proposition 6.11), so the fallback is never used
--   - reading: Line 23 of Algorithm 4 updates F̂_t, Ŝ_t on the active sets only → F̂_t(b) = (1/t) Σ_{τ≤t} χ^sell_τ(b) and Ŝ_t(a) = (1/t) Σ_{τ≤t} χ^buy_τ(a) for every price, with F̂_0 = Ŝ_0 = 0; reason: Algorithm 5 evaluates the bounds only on the active sets, which are nested, so the values the algorithm uses are the same
--   - reading: S(a) = E[I(V^buy ≥ a)] = 1 − F_buy(a) (p. 16) → S(a) = P(V^buy ≥ a); reason: the two expressions differ exactly at atoms of V^buy; the trade probability E[I(V^buy ≥ a)] is what the model and every proof use (p. 59 also writes S(a) = P(−V^buy ≤ −a))
--   - generalization: rounds whose valuation pairs are i.i.d. from the valuation law V of Sec. 3 (supported in [0, 1]², P(V^buy = 1) = P(V^sell = 0) = 0) → any probability law V on ℝ² and arbitrary real valuation and draw sequences (no probability model); reason: the claim is pathwise on the good event and uses only that F and S take values in [0, 1]; the paper's model is an instance
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Theorem 6.15, p. 44

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_J
import Definitions.Def_InvMarketMaking_LOB_IsGridOpt
import Definitions.Def_InvMarketMaking_LOB_lobRound
import Definitions.Def_InvMarketMaking_LOB_goodEvent

open MeasureTheory ProbabilityTheory

namespace InvMarketMaking.LOB

/-- **Theorem 6.15** (Maran, Restelli, Stradi, arXiv:2610.24562v1, p. 44). Under the good event,
the pair `b°, a°` of Definition 4.4 never gets eliminated: for every round `t ∈ [T]`,
`B_{t,0} ≤ b°` and `a° ≤ A_{t,0}`, i.e. `b° ∈ B°_t` and `a° ∈ A°_t`.

**Formalization Note** `(b°, a°)` is any maximizer of `J` on `B° × A°` (every tie-break, p. 19);
if `max J = 0` it may have `b° ≥ a°`. Stated for Algorithm 4 with grids in `[0,1]` containing a
pair `b < a` and nonnegative radii, for every outcome of the good event. -/
theorem theorem_6_15 {Ω : Type*} (V : Measure (ℝ × ℝ)) [IsProbabilityMeasure V] (C : LOBConfig Ω)
    (M : Market Ω) (hB : ↑C.Bg ⊆ Set.Icc (0 : ℝ) 1) (hA : ↑C.Ag ⊆ Set.Icc (0 : ℝ) 1)
    (hfeas : ∃ b ∈ C.Bg, ∃ a ∈ C.Ag, b < a)
    (hψF : ∀ t x ω, 0 ≤ C.ψF t x ω) (hψS : ∀ t x ω, 0 ≤ C.ψS t x ω)
    (bo ao : ℝ) (hopt : IsGridOpt V C.Bg C.Ag bo ao) (T : ℕ) (ω : Ω)
    (hω : ω ∈ goodEvent V C M T) (t : ℕ) (ht : t ∈ Finset.Icc 1 T) :
    (lobRound C M t ω).bid0 ≤ bo ∧ ao ≤ (lobRound C M t ω).ask0 := by sorry

end InvMarketMaking.LOB
