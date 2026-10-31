-- Prove2me | Theorems.Thm_NieYangPareto_dual_nonneg_cone_eq_closure_momentCone
-- name    : NieYangPareto.dual_nonneg_cone_eq_closure_momentCone
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:02:46.12026+00:00
-- url     : https://prove2.me/theorems/023bfd73-7766-4fd6-9bf1-9764d766fddc
-- title:
--   §3.2 after (3.2) — the dual cone of $\mathscr P_d(K)$ is $\operatorname{cl}(\mathscr R_d(K))$
-- statement:
--   For the feasible set $K$ of (1.1) and every degree $d$, the dual cone of the nonnegative polynomial cone is the closure of the moment cone:
--
--   $$
--   \operatorname{cl}(\mathscr R_d(K))=\{y\in\mathbb R^{\mathbb N^n_d}:\ \langle p,y\rangle\ge0\ \ \forall p\in\mathscr P_d(K)\}.
--   $$
--
--   This is what makes (3.3) the dual program of (3.2).
--
--   Differences from the source:
--   - encoding: disjoint finite label sets ℰ, ℐ → two finite types E, I (`[Finite E] [Finite I]`), each with its own constraint family; reason: separate types encode disjointness; the same instances
--   - encoding: tms y ∈ ℝ^{ℕⁿ_d} → y : TmsIndex n d → ℝ, on the finite subtype {α : Fin n →₀ ℕ // α.degree ≤ d}, with the product topology; reason: the same finite-dimensional Euclidean space
--   - encoding: y = ∫[x]_d dμ in (2.2) → each monomial of degree ≤ d is μ-integrable and y_α = ∫x^α dμ; reason: this is what the page's equation means; it stops the junk value ∫ = 0 from entering
--   - encoding: "the dual cone of 𝒫_d(K)" → the set of y with ⟨p, y⟩ ≥ 0 for all p ∈ 𝒫_d(K); reason: the definition of a dual cone, for the pairing (2.1)
--   - generalization: d the maximum degree of the objectives f_i (p.8) → any degree d; reason: §2.2 (p.5) states the same sentence for every degree d, and at d = max_i deg f_i it is the p.8 statement
-- source:
--   Nie–Yang, The multi-objective polynomial optimization, arXiv:2108.04336v2, §3.2 after (3.2), p.8; also §2.2, p.5

import Mathlib
import Definitions.Def_NieYangPareto_MOP
import Definitions.Def_NieYangPareto_Tms
import Definitions.Def_NieYangPareto_momentCone
import Definitions.Def_NieYangPareto_nonnegCone

namespace NieYangPareto

/-- **The dual cone of `𝒫_d(K)` is `cl(ℛ_d(K))`.** Nie–Yang, arXiv:2108.04336v2, §3.2 after (3.2),
p.8 (also §2.2, p.5): "The dual cone of 𝒫_d(K) is the closure cl(ℛ_d(K)), where ℛ_d(K) is the moment
cone as in (2.2)."

**Formalization Note** The dual cone is the set of `y ∈ ℝ^{ℕⁿ_d}` with `⟨p, y⟩ ≥ 0` for all
`p ∈ 𝒫_d(K)`, for the pairing (2.1). -/
theorem dual_nonneg_cone_eq_closure_momentCone {n m : ℕ} {E I : Type*} [Finite E] [Finite I]
    (P : MOP n m E I) (d : ℕ) :
    closure (momentCone P.K d) = {y : Tms n d | ∀ p ∈ nonnegCone P.K d, 0 ≤ pair p y} := by sorry

end NieYangPareto
