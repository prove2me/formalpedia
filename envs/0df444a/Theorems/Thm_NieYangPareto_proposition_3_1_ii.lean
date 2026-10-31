-- Prove2me | Theorems.Thm_NieYangPareto_proposition_3_1_ii
-- name    : NieYangPareto.proposition_3_1_ii
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:03:17.101578+00:00
-- url     : https://prove2.me/theorems/8a518a05-e580-4469-a8ef-b20e61bafd82
-- title:
--   Proposition 3.1(ii) — for convex $\mathcal U$, a WPV has a supporting hyperplane with nonnegative normal
-- statement:
--   Let $v\in f(K)$ and assume $\mathcal U$ is convex. If $v$ is a weakly Pareto value, then there exists a supporting hyperplane for $\mathcal U$ through $v$ whose normal is nonnegative: there exists $0\ne w\ge0$ such that
--
--   $$
--   w^Tu\ge w^Tv\quad\text{for all }u\in\mathcal U .
--   $$
--
--   So on a convex epigraph set, weakly Pareto values are the values reached by nonnegative linear scalarizations.
--
--   Differences from the source:
--   - encoding: disjoint finite label sets ℰ, ℐ → two finite types E, I (`[Finite E] [Finite I]`), each with its own constraint family; reason: separate types encode disjointness; the same instances
--   - encoding: "a supporting hyperplane for 𝒰 through v whose normal is nonnegative, i.e., there exists 0 ≠ w ≥ 0 such that wᵀu ≥ wᵀv for all u ∈ 𝒰" → the "i.e." clause, verbatim; reason: the page states the two as equivalent, and v ∈ f(K) ⊆ 𝒰
-- source:
--   Nie–Yang, The multi-objective polynomial optimization, arXiv:2108.04336v2, Proposition 3.1(ii), p.6

import Mathlib
import Definitions.Def_NieYangPareto_MOP
import Definitions.Def_NieYangPareto_ParetoNotions
import Definitions.Def_NieYangPareto_MOP_U

namespace NieYangPareto

/-- **Proposition 3.1(ii).** Nie–Yang, arXiv:2108.04336v2, Proposition 3.1(ii), p.6: for `v ∈ f(K)`,
assume `𝒰` is convex. If `v` is a WPV, then there exists `0 ≠ w ≥ 0` such that `wᵀu ≥ wᵀv` for all
`u ∈ 𝒰`. -/
theorem proposition_3_1_ii {n m : ℕ} {E I : Type*} [Finite E] [Finite I]
    (P : MOP n m E I)
    (v : Fin m → ℝ) (hv : v ∈ P.obj '' P.K) (hU : Convex ℝ P.U)
    (hWPV : P.IsWeaklyParetoValue v) :
    ∃ w : Fin m → ℝ, w ≠ 0 ∧ 0 ≤ w ∧ ∀ u ∈ P.U, w ⬝ᵥ v ≤ w ⬝ᵥ u := by sorry

end NieYangPareto
