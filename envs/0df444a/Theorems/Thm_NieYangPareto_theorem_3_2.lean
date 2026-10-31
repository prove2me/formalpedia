-- Prove2me | Theorems.Thm_NieYangPareto_theorem_3_2
-- name    : NieYangPareto.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:13.517358+00:00
-- url     : https://prove2.me/theorems/0921a913-7d64-4f28-b168-5a4ccab8327f
-- title:
--   Theorem 3.2 — $\operatorname{int}\operatorname{conv}(\mathcal U)=\mathcal V$, and weakly Pareto values are the boundary of $\operatorname{cl}(\mathcal V)$
-- statement:
--   Consider the multi-objective polynomial optimization problem (1.1), with feasible set $K$, epigraph set $\mathcal U$ as in (3.1), and $\mathcal V$ as in (3.4). Assume $K$ has nonempty interior. Then
--
--   $$
--   \operatorname{int}\operatorname{conv}(\mathcal U)=\mathcal V .
--   $$
--
--   Moreover, when $\mathcal U$ is convex, a vector $v\in f(K)$ is a weakly Pareto value if and only if $v$ belongs to the boundary of the closure $\operatorname{cl}(\mathcal V)$.
--
--   This represents the weakly Pareto front through the boundary of a convex set described by moments. It is the paper's geometric result on Pareto values.
--
--   Differences from the source:
--   - encoding: disjoint finite label sets ℰ, ℐ → two finite types E, I (`[Finite E] [Finite I]`), each with its own constraint family; reason: separate types encode disjointness; the same instances
--   - encoding: tms y ∈ ℝ^{ℕⁿ_d} → y : TmsIndex n d → ℝ, on the finite subtype {α : Fin n →₀ ℕ // α.degree ≤ d}, with the product topology; reason: the same finite-dimensional Euclidean space
--   - encoding: y = ∫[x]_d dμ in (2.2) → each monomial of degree ≤ d is μ-integrable and y_α = ∫x^α dμ; reason: this is what the page's equation means; it stops the junk value ∫ = 0 from entering
-- source:
--   Nie–Yang, The multi-objective polynomial optimization, arXiv:2108.04336v2, Theorem 3.2, p.9

import Mathlib
import Definitions.Def_NieYangPareto_MOP
import Definitions.Def_NieYangPareto_ParetoNotions
import Definitions.Def_NieYangPareto_MOP_U
import Definitions.Def_NieYangPareto_MOP_V

namespace NieYangPareto

/-- **Theorem 3.2.** Nie–Yang, arXiv:2108.04336v2, Theorem 3.2, p.9: assume `K` has nonempty
interior. Then the interior of the convex hull `conv(𝒰)` is the set `𝒱` as in (3.4). Moreover, when
`𝒰` is convex, a vector `v ∈ f(K)` is a weakly Pareto value if and only if `v` belongs to the
boundary of the closure `cl(𝒱)`.

**Formalization Note** `K`, `𝒰`, `𝒱` are `P.K`, `P.U`, `P.V`, and `d` inside `𝒱` is the maximum degree
of the objectives, as on p.8. -/
theorem theorem_3_2 {n m : ℕ} {E I : Type*} [Finite E] [Finite I]
    (P : MOP n m E I)
    (hK : (interior P.K).Nonempty) :
    interior (convexHull ℝ P.U) = P.V ∧
      (Convex ℝ P.U →
        ∀ v ∈ P.obj '' P.K, P.IsWeaklyParetoValue v ↔ v ∈ frontier (closure P.V)) := by sorry

end NieYangPareto
