-- Prove2me | Theorems.Thm_HartSchmeidler_Compact_theorem_3
-- name    : HartSchmeidler.Compact.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:14:58.718358+00:00
-- url     : https://prove2.me/theorems/361f43e2-2ecd-42e9-ac0a-96e3e8bf6e3b
-- title:
--   Theorem 3 — compact Hausdorff strategy spaces and continuous payoffs give a countably additive correlated equilibrium
-- statement:
--   Let $N$ be a nonempty set of players, possibly uncountable. Assume that for each $i\in N$ the strategy space $S^i$ is a nonempty compact Hausdorff space and the payoff function $h^i:S\to\mathbb R$ is continuous, where $S=\prod_{j\in N}S^j$ is endowed with the product topology. Let $\Sigma^i$ be the Borel σ-algebra on $S^i$ and $\Sigma$ the Borel σ-algebra on $S$. Then there exists a countably additive probability measure $p$ on $(S,\Sigma)$ that is a correlated equilibrium with respect to $\{\Sigma^i\}_{i\in N}$ and $\Sigma$: for every player $i$ and every $\Sigma^i$-measurable $\zeta^i:S^i\to S^i$,
--   $$
--   \int_S\bigl[h^i(s^{-i},s^i)-h^i\bigl(s^{-i},\zeta^i(s^i)\bigr)\bigr]\,dp(s)\ \ge\ 0 .
--   $$
--
--   The theorem extends the existence of correlated equilibria from finite games to games with arbitrarily many players and compact strategy spaces, and it does so without a fixed-point theorem.
--
--   **Formalization Note** $\Sigma$ is the Borel σ-algebra of the product topology on the type synonym `Profile S`, not the product σ-algebra $\Sigma_0=\bigotimes_i\Sigma^i$; footnote 13 notes that $\Sigma\supseteq\Sigma_0$ with possibly strict inclusion when $S$ is not metrizable. Measurable deviations range over all Borel-measurable maps, not only continuous ones. The definition of a correlated equilibrium also requires each integrand to be integrable, which rules out a vacuous satisfaction of (4) through Lean's convention that the integral of a non-integrable function is $0$. Nonemptiness of $N$ and of each $S^i$ is part of the paper's definition of a game (§3).
-- source:
--   Hart and Schmeidler, Existence of Correlated Equilibria, Math. Oper. Res. 14 (1989), p. 24, Theorem 3 (with footnote 13); https://doi.org/10.1287/moor.14.1.18

import Definitions.Def_HartSchmeidler_Compact_Game

namespace HartSchmeidler.Compact

open MeasureTheory

/-- Theorem 3, p. 24: if every strategy space `Sⁱ` is compact Hausdorff and every payoff `hⁱ`
is continuous on `S` with the product topology, then there is a countably additive correlated
equilibrium with respect to the Borel σ-algebras `Σⁱ` on `Sⁱ` and `Σ` on `S`. -/
theorem theorem_3 {ι : Type*} [Nonempty ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)] [∀ i, T2Space (S i)]
    [∀ i, Nonempty (S i)] [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    (h : ι → Profile S → ℝ) (hcont : ∀ i, Continuous (h i)) :
    ∃ μ : Measure (Profile S), IsCorrelatedEq h μ := by sorry

end HartSchmeidler.Compact
