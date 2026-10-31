-- Prove2me | Theorems.Thm_KnapsackFacets_statement_ii
-- name    : KnapsackFacets.statement_ii
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:15:12.14055+00:00
-- url     : https://prove2.me/theorems/83bd383f-3a41-4dc9-8488-77456638e3a1
-- title:
--   Theorem 4, proof, (ii) — $N$ affinely independent tight points iff some $S$ has $w(S)=t-1$
-- statement:
--   Let $(w,t)$ be a CSS instance with $w_i\le t-1$ for all $i$ and $t\ge2$, let $a,b,\alpha,\beta$ be the instance (3)–(6), and $N=2r+n+4$. Then there are $N$ affinely independent points in
--   $$
--   \{x\in\{0,1\}^N:\ a^\top x\le b,\ \alpha^\top x=\beta\}
--   $$
--   if and only if there is a subset $S\subseteq[n]$ with $w(S)=t-1$.
--
--   This is the NP half of the correctness of the reduction in Theorem 4.
--
--   Differences from the source:
--   - encoding: wᵢ ≤ t − 1 for all i ∈ [n] and t ≥ 2 → hypotheses ∀ i, w i + 1 ≤ t and 2 ≤ t, with w : Fin n → ℕ, t : ℕ; reason: the proof's standing assumptions, written without natural-number subtraction
--   - encoding: N affinely independent points; w(S) = t − 1 → a family v : Fin N → (Fin N → ℝ) with AffineIndependent ℝ v; w(S) + 1 = t; reason: the same statement without natural-number subtraction
--   - encoding: coordinates x₁, …, x_N → 0-based coordinates: the paper's x_{i+1} is x i : Fin _, and coefficients take i.val + 1; reason: a Lean convention; the same points and the same coefficients
-- source:
--   Chen & Zhu, The Complexity of Recognizing Facets for the Knapsack Polytope, arXiv:2211.03311v3, Theorem 4, proof, (ii), p.12 (argument pp.11–12)

import Definitions.Def_KnapsackFacets_KnapsackPolytope
import Definitions.Def_KnapsackFacets_Reduction

set_option autoImplicit false

namespace KnapsackFacets

/-- **(ii), p.12.** "There exist N affinely independent points in {x ∈ {0, 1}ᴺ : a⊤x ≤ b,
α⊤x = β} if and only if there exists subset S ⊆ [n] such that w(S) = t − 1." Chen & Zhu,
arXiv:2211.03311v3, Theorem 4, proof, (ii), p.12.

`a, b, α, β` and `N = 2r + n + 4` are the reduction instance (3)–(6) built from `(w, t)`,
under the standing assumptions `wᵢ ≤ t − 1` for all `i` and `t ≥ 2` (p.6).

**Formalization Note.** `N` points are a family `v : Fin N → (Fin N → ℝ)`, affinely
independent over `ℝ`, each in the knapsack set `{x ∈ {0,1}ᴺ : aᵀx ≤ b}` and on `αᵀx = β`.
`w(S) = t − 1` is written `w(S) + 1 = t` (no natural-number subtraction). -/
theorem statement_ii {n : ℕ} (w : Fin n → ℕ) (t : ℕ) (ht : 2 ≤ t) (hw : ∀ i, w i + 1 ≤ t) :
    (∃ v : Fin (redN w) → (Fin (redN w) → ℝ), AffineIndependent ℝ v ∧
        ∀ k, v k ∈ knapsackSet (redA w t) (redB w t) ∧
          ∑ i, ((redAlpha w t i : ℤ) : ℝ) * v k i = ((redBeta w t : ℕ) : ℝ)) ↔
      ∃ S : Finset (Fin n), ∑ i ∈ S, w i + 1 = t := by sorry

end KnapsackFacets
