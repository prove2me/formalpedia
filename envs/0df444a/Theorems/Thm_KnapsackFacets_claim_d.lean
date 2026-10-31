-- Prove2me | Theorems.Thm_KnapsackFacets_claim_d
-- name    : KnapsackFacets.claim_d
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:14:48.092485+00:00
-- url     : https://prove2.me/theorems/6136b37b-5b94-4bfa-8952-9cea430d5758
-- title:
--   Theorem 4, proof, Claim D — the inequality on the first $2r+n+2$ coordinates is facet-defining
-- statement:
--   Let $(w,t)$ be a CSS instance with $w_i\le t-1$ for all $i$ and $t\ge2$, and let $a,\alpha,r$ be as in (3), (5) of the proof of Theorem 4. The inequality
--   $$
--   \sum_{i=1}^{2r+n+2}\alpha_ix_i\ \le\ \sum_{i=1}^{2r}f_i
--   $$
--   is facet-defining for the knapsack polytope
--   $$
--   \operatorname{conv}\Big(\Big\{x\in\{0,1\}^{2r+n+2}:\ \sum_{i=1}^{2r+n+2}a_ix_i\le\sum_{i=1}^{2r}tf_i\Big\}\Big).
--   $$
--
--   This is the restriction of the reduction instance to $x_{N-1}=x_N=0$, up to the right-hand sides; cases (a) and the point family of (ii) rest on it.
--
--   Differences from the source:
--   - encoding: wᵢ ≤ t − 1 for all i ∈ [n] and t ≥ 2 → hypotheses ∀ i, w i + 1 ≤ t and 2 ≤ t, with w : Fin n → ℕ, t : ℕ; reason: the proof's standing assumptions, written without natural-number subtraction
--   - encoding: coordinates x₁, …, x_{2r+n+2} → 0-based coordinates: the paper's x_{i+1} is x i : Fin _, and coefficients take i.val + 1; reason: a Lean convention; the same points and the same coefficients
--   - reading: facet-defining: "essentially a valid inequality that holds at equality at dim(P) affinely independent points in P" (p.2) → IsFacetDefining: valid, nonempty face F, and dim F + 1 = dim P (finrank of vector spans); reason: the standard notion; read literally, p.2 would make 0ᵀx ≤ 0 facet-defining for every polytope
-- source:
--   Chen & Zhu, The Complexity of Recognizing Facets for the Knapsack Polytope, arXiv:2211.03311v3, Theorem 4, proof, Claim D (fourth Claim), p.8 (proof pp.8–9)

import Definitions.Def_KnapsackFacets_KnapsackPolytope
import Definitions.Def_KnapsackFacets_Reduction

set_option autoImplicit false

namespace KnapsackFacets

/-- **Claim D (fourth Claim in the proof of Theorem 4).** "Inequality
Σ_{i=1}^{2r+n+2} αᵢxᵢ ≤ Σ_{i=1}^{2r} fᵢ is a facet-defining inequality for the KP
conv({x ∈ {0, 1}^{2r+n+2} : Σ_{i=1}^{2r+n+2} aᵢxᵢ ≤ Σ_{i=1}^{2r} tfᵢ})." Chen & Zhu,
arXiv:2211.03311v3, Theorem 4, proof, Claim D, p.8 (proof pp.8–9).

Here `a`, `α` are (3), (5) for the CSS instance `(w, t)`, restricted to the first `2r + n + 2`
coordinates, under the standing assumptions `wᵢ ≤ t − 1` for all `i` and `t ≥ 2` (p.6).

**Formalization Note.** Coordinate `i : Fin (2r+n+2)` is the paper's `x_{i+1}`; `wᵢ ≤ t − 1`
is written `w i + 1 ≤ t`; weights `wᵢ = 0` are allowed (then `aᵢ = 0`). -/
theorem claim_d {n : ℕ} (w : Fin n → ℕ) (t : ℕ) (ht : 2 ≤ t) (hw : ∀ i, w i + 1 ≤ t) :
    IsFacetDefining (fun i : Fin (2 * redR w + n + 2) => aCoef w t (i.val + 1))
      (t * ∑ i ∈ Finset.Icc 1 (2 * redR w), shiftedFib i)
      (fun i : Fin (2 * redR w + n + 2) => (alphaCoef w t (i.val + 1) : ℤ))
      ((∑ i ∈ Finset.Icc 1 (2 * redR w), shiftedFib i : ℕ) : ℤ) := by sorry

end KnapsackFacets
