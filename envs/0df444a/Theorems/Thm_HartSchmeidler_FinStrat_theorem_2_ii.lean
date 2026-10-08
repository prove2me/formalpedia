-- Prove2me | Theorems.Thm_HartSchmeidler_FinStrat_theorem_2_ii
-- name    : HartSchmeidler.FinStrat.theorem_2_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:09:23.614759+00:00
-- url     : https://prove2.me/theorems/458c71a2-234c-460b-826f-0db39d356fb1
-- title:
--   Theorem 2(ii) — countably additive correlated equilibrium for continuous payoffs
-- statement:
--   Let $N$ be any nonempty set of players, with no finiteness or countability restriction on $N$. Every player $i$ has a nonempty finite set $S^i$ of pure strategies, equipped with the discrete topology, and a continuous payoff $h^i:S=\prod_{j\in N}S^j\to\mathbb R$. Then there is a countably additive probability measure $p$ on the product σ-algebra $\Sigma_0$ such that, for every $i\in N$ and $r^i,t^i\in S^i$, the payoff difference is integrable on $\{s:s^i=r^i\}$ and
--
--   $$\int_{\{s:s^i=r^i\}}\bigl[h^i(s)-h^i(s^{-i},t^i)\bigr]\,dp(s)\ge0.$$
--
--   Thus a correlated recommendation scheme exists even with arbitrarily many players, provided each strategy set is finite and payoffs are continuous.
--
--   **Formalization Note.** The product measurable structure is $\Sigma_0$; it can be strictly smaller than the Borel σ-algebra when the player set is uncountable. The unilateral deviation replaces only coordinate $i$. Continuity on the compact product supplies the boundedness and measurability assumed in §3, while integrability is made explicit to exclude Lean's default zero integral for nonintegrable functions.
-- source:
--   Hart and Schmeidler, Existence of Correlated Equilibria, Math. Oper. Res. 14 (1989), p. 21, Theorem 2(ii)

import Definitions.Def_HartSchmeidler_FinStrat_Game

namespace HartSchmeidler.FinStrat

open MeasureTheory

/-- Hart and Schmeidler (1989), Theorem 2(ii), p. 21. -/
theorem theorem_2_ii {ι : Type*} [Nonempty ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Nonempty (S i)]
    [∀ i, TopologicalSpace (S i)] [∀ i, DiscreteTopology (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, DiscreteMeasurableSpace (S i)]
    (h : ι → (∀ i, S i) → ℝ) (hh : ∀ i, Continuous (h i)) :
    ∃ μ : Measure (∀ i, S i), IsCorrelatedEq h μ := by sorry

end HartSchmeidler.FinStrat
