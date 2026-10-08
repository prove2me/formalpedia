-- Prove2me | Theorems.Thm_HartSchmeidler_Compact_cond3_iff_cond4_of_finite
-- name    : HartSchmeidler.Compact.cond3_iff_cond4_of_finite
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:14:13.99001+00:00
-- url     : https://prove2.me/theorems/b59a7464-f8f0-42cc-b03a-84202d870bc4
-- title:
--   p. 23 — for a finite strategy set, conditions (3) and (4) are equivalent
-- statement:
--   Let $N$ be a set of players, each strategy space $S^i$ a topological space with its Borel σ-algebra, and let $S=\prod_jS^j$ carry the product topology and its Borel σ-algebra $\Sigma$. Fix a player $i$ whose strategy set $S^i$ is finite and discrete, assume $h^i$ is bounded and $\Sigma$-measurable, and let $p$ be a probability measure on $(S,\Sigma)$. Then condition (3) for player $i$,
--   $$
--   \int_{S^{-i}\times\{r^i\}}\bigl[h^i(s^{-i},r^i)-h^i(s^{-i},t^i)\bigr]\,dp(s)\ \ge 0\qquad\text{for all } r^i,t^i\in S^i,
--   $$
--   holds if and only if condition (4) for player $i$,
--   $$
--   \int_S\bigl[h^i(s^{-i},s^i)-h^i\bigl(s^{-i},\zeta^i(s^i)\bigr)\bigr]\,dp(s)\ \ge 0\qquad\text{for all measurable }\zeta^i:S^i\to S^i,
--   $$
--   holds.
--
--   This shows that (4), the definition of a correlated equilibrium used for infinite strategy sets, reduces to the earlier condition (3) whenever a player's strategy set is finite, so §4 extends §3.
--
--   **Formalization Note** $S^{-i}\times\{r^i\}$ is the set of profiles $s$ with $s^i=r^i$. The finite strategy set carries the discrete topology, so every subset of $S^i$ and every map $\zeta^i$ is measurable. With $h^i$ bounded and measurable all the integrands are integrable, so the integrability requirement of the definition is not repeated here.
-- source:
--   Hart and Schmeidler, Existence of Correlated Equilibria, Math. Oper. Res. 14 (1989), p. 23, §4 ("It is easy to see that, when S^i is a finite set, conditions (4) and (3) are equivalent"); condition (3) is on p. 21; https://doi.org/10.1287/moor.14.1.18

import Definitions.Def_HartSchmeidler_Compact_Game

namespace HartSchmeidler.Compact

open MeasureTheory

/-- p. 23: when the strategy set `Sⁱ` of player `i` is finite, condition (3) for player `i`
(one inequality per recommendation `r` and deviation `t`) is equivalent to condition (4) for
player `i` (one inequality per measurable deviation map `ζ : Sⁱ → Sⁱ`). -/
theorem cond3_iff_cond4_of_finite {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    [∀ j, TopologicalSpace (S j)] [∀ j, MeasurableSpace (S j)] [∀ j, BorelSpace (S j)]
    (h : ι → Profile S → ℝ) (i : ι) [Fintype (S i)] [DiscreteTopology (S i)]
    (hmeas : Measurable (h i)) (hbdd : ∃ M : ℝ, ∀ s, |h i s| ≤ M)
    (p : Measure (Profile S)) [IsProbabilityMeasure p] :
    (∀ r t : S i,
        0 ≤ ∫ s in {s : Profile S | s i = r}, (h i s - h i (Function.update s i t)) ∂p) ↔
      (∀ ζ : S i → S i, Measurable ζ →
        0 ≤ ∫ s : Profile S, (h i s - h i (Function.update s i (ζ (s i)))) ∂p) := by sorry

end HartSchmeidler.Compact
