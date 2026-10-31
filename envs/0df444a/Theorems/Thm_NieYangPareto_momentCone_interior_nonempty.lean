-- Prove2me | Theorems.Thm_NieYangPareto_momentCone_interior_nonempty
-- name    : NieYangPareto.momentCone_interior_nonempty
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:02:53.452761+00:00
-- url     : https://prove2.me/theorems/f2d0d612-55ad-4902-a85d-f8f86bad22dc
-- title:
--   Proof of Theorem 3.2 — $\mathscr R_d(K)$ has nonempty interior
-- statement:
--   If the feasible set $K$ of (1.1) has nonempty interior, then for every degree $d$ the moment cone $\mathscr R_d(K)$ has nonempty interior in $\mathbb R^{\mathbb N^n_d}$.
--
--   This is the Slater condition behind the strong duality of (3.2) and (3.3).
--
--   Differences from the source:
--   - encoding: disjoint finite label sets ℰ, ℐ → two finite types E, I (`[Finite E] [Finite I]`), each with its own constraint family; reason: separate types encode disjointness; the same instances
--   - encoding: tms y ∈ ℝ^{ℕⁿ_d} → y : TmsIndex n d → ℝ, on the finite subtype {α : Fin n →₀ ℕ // α.degree ≤ d}, with the product topology; reason: the same finite-dimensional Euclidean space
--   - encoding: y = ∫[x]_d dμ in (2.2) → each monomial of degree ≤ d is μ-integrable and y_α = ∫x^α dμ; reason: this is what the page's equation means; it stops the junk value ∫ = 0 from entering
--   - generalization: d the maximum degree of the objectives f_i (p.8, used on p.9) → any degree d; reason: the statement for every d specializes to the page's at d = max_i deg f_i
-- source:
--   Nie–Yang, The multi-objective polynomial optimization, arXiv:2108.04336v2, proof of Theorem 3.2, p.9

import Mathlib
import Definitions.Def_NieYangPareto_MOP
import Definitions.Def_NieYangPareto_Tms
import Definitions.Def_NieYangPareto_momentCone

namespace NieYangPareto

/-- **`ℛ_d(K)` has nonempty interior.** Nie–Yang, arXiv:2108.04336v2, proof of Theorem 3.2, p.9:
"Since K has nonempty interior, the cone ℛ_d(K) has nonempty interior."

**Formalization Note** The interior is in the product topology of `ℝ^{ℕⁿ_d}`; the degree `d` is
arbitrary. -/
theorem momentCone_interior_nonempty {n m : ℕ} {E I : Type*} [Finite E] [Finite I]
    (P : MOP n m E I) (d : ℕ)
    (hK : (interior P.K).Nonempty) :
    (interior (momentCone P.K d)).Nonempty := by sorry

end NieYangPareto
