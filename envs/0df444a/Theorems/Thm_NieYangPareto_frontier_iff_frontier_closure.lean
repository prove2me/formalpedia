-- Prove2me | Theorems.Thm_NieYangPareto_frontier_iff_frontier_closure
-- name    : NieYangPareto.frontier_iff_frontier_closure
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:03:42.169988+00:00
-- url     : https://prove2.me/theorems/00e87a89-d955-47b9-9de4-1d836eaf5dd5
-- title:
--   Proof of Theorem 3.2 — for convex $\mathcal U$ and $v\in f(K)$, boundary of $\mathcal U$ iff boundary of $\operatorname{cl}(\mathcal V)$
-- statement:
--   Let $K$ have nonempty interior, assume $\mathcal U$ is convex, and let $v\in f(K)$. Then $v$ lies on the boundary of $\mathcal U$ if and only if $v$ lies on the boundary of the closure $\operatorname{cl}(\mathcal V)$.
--
--   With Proposition 3.1(i) this gives the second clause of Theorem 3.2.
--
--   Differences from the source:
--   - encoding: disjoint finite label sets ℰ, ℐ → two finite types E, I (`[Finite E] [Finite I]`), each with its own constraint family; reason: separate types encode disjointness; the same instances
--   - encoding: tms y ∈ ℝ^{ℕⁿ_d} → y : TmsIndex n d → ℝ, on the finite subtype {α : Fin n →₀ ℕ // α.degree ≤ d}, with the product topology; reason: the same finite-dimensional Euclidean space
--   - encoding: y = ∫[x]_d dμ in (2.2) → each monomial of degree ≤ d is μ-integrable and y_α = ∫x^α dμ; reason: this is what the page's equation means; it stops the junk value ∫ = 0 from entering
-- source:
--   Nie–Yang, The multi-objective polynomial optimization, arXiv:2108.04336v2, proof of Theorem 3.2, p.9

import Mathlib
import Definitions.Def_NieYangPareto_MOP
import Definitions.Def_NieYangPareto_MOP_U
import Definitions.Def_NieYangPareto_MOP_V

namespace NieYangPareto

/-- **Boundary of `𝒰` and boundary of `cl(𝒱)`.** Nie–Yang, arXiv:2108.04336v2, proof of Theorem 3.2,
p.9: when `𝒰` is convex, for `v ∈ f(K)`, that `v` lies on the boundary of `𝒰` "is equivalent to that
v lies on the boundary of cl(𝒱), since the interior of 𝒰 is 𝒱." -/
theorem frontier_iff_frontier_closure {n m : ℕ} {E I : Type*} [Finite E] [Finite I]
    (P : MOP n m E I)
    (hK : (interior P.K).Nonempty) (hU : Convex ℝ P.U)
    (v : Fin m → ℝ) (hv : v ∈ P.obj '' P.K) :
    v ∈ frontier P.U ↔ v ∈ frontier (closure P.V) := by sorry

end NieYangPareto
