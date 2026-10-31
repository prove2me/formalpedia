-- Prove2me | Theorems.Thm_KnapsackFacets_claim_b
-- name    : KnapsackFacets.claim_b
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:13:24.311089+00:00
-- url     : https://prove2.me/theorems/55f405a3-415b-44e7-b39d-dee17c2d41b1
-- title:
--   Theorem 4, proof, Claim B — the inequality on the first $2r+1$ coordinates is facet-defining
-- statement:
--   Let $r\ge1$ and $t\ge1$ be integers and $f$ the shifted Fibonacci sequence of (1)–(2). The inequality
--   $$
--   \sum_{i=1}^{2r+1}f_ix_i\ \le\ \sum_{i=1}^{2r}f_i
--   $$
--   is facet-defining for the knapsack polytope
--   $$
--   \operatorname{conv}\Big(\Big\{x\in\{0,1\}^{2r+1}:\ \sum_{i=1}^{2r+1}tf_ix_i\le\sum_{i=1}^{2r}tf_i\Big\}\Big).
--   $$
--
--   In the reduction of Theorem 4, $a_i=tf_i$ and $\alpha_i=f_i$ for $i\le2r+1$, so this is the first of the three Claims building a facet coordinate block by coordinate block.
--
--   Differences from the source:
--   - generalization: the r = ⌈log₂(30L + 20) − 1⌉ and the target t ≥ 2 of the CSS instance → every integer r ≥ 1 and every integer t ≥ 1; reason: the coefficients aᵢ = t fᵢ, αᵢ = fᵢ (i ≤ 2r + 1) depend only on r and t, and the paper's proof is for every r ("a stronger version", γ = 1, …, r); the paper's r ≥ 4 and t ≥ 2 are instances
--   - encoding: coordinates x₁, …, x_{2r+1} → 0-based coordinates: the paper's x_{i+1} is x i : Fin _, and coefficients take i.val + 1; reason: a Lean convention; the same points and the same coefficients
--   - reading: facet-defining: "essentially a valid inequality that holds at equality at dim(P) affinely independent points in P" (p.2) → IsFacetDefining: valid, nonempty face F, and dim F + 1 = dim P (finrank of vector spans); reason: the standard notion; read literally, p.2 would make 0ᵀx ≤ 0 facet-defining for every polytope
-- source:
--   Chen & Zhu, The Complexity of Recognizing Facets for the Knapsack Polytope, arXiv:2211.03311v3, Theorem 4, proof, Claim B (second Claim), p.7

import Definitions.Def_KnapsackFacets_KnapsackPolytope
import Definitions.Def_KnapsackFacets_ShiftedFib

set_option autoImplicit false

namespace KnapsackFacets

/-- **Claim B (second Claim in the proof of Theorem 4).** "Inequality
Σ_{i=1}^{2r+1} αᵢxᵢ ≤ Σ_{i=1}^{2r} fᵢ is a facet-defining inequality for the KP
conv({x ∈ {0, 1}^{2r+1} : Σ_{i=1}^{2r+1} aᵢxᵢ ≤ Σ_{i=1}^{2r} tfᵢ})." Chen & Zhu,
arXiv:2211.03311v3, Theorem 4, proof, Claim B, p.7.

On the first `2r + 1` coordinates the reduction has `aᵢ = t fᵢ` and `αᵢ = fᵢ` (p.6, (3), (5)),
which depend only on `r` and `t`. The statement is made for every `r ≥ 1` and every `t ≥ 1`.

**Formalization Note.** Coordinate `i : Fin (2r+1)` is the paper's `x_{i+1}`, so its
coefficients are `t · f_{i+1}` and `f_{i+1}`. -/
theorem claim_b (r : ℕ) (hr : 1 ≤ r) (t : ℕ) (ht : 1 ≤ t) :
    IsFacetDefining (fun i : Fin (2 * r + 1) => t * shiftedFib (i.val + 1))
      (t * ∑ i ∈ Finset.Icc 1 (2 * r), shiftedFib i)
      (fun i : Fin (2 * r + 1) => (shiftedFib (i.val + 1) : ℤ))
      ((∑ i ∈ Finset.Icc 1 (2 * r), shiftedFib i : ℕ) : ℤ) := by sorry

end KnapsackFacets
