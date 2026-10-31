-- Prove2me | Theorems.Thm_KnapsackFacets_statement_i
-- name    : KnapsackFacets.statement_i
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:14:57.0733+00:00
-- url     : https://prove2.me/theorems/11c59efe-3497-45b1-b6b1-83872c483762
-- title:
--   Theorem 4, proof, (i) — no $T$ with $w(T)=t$ iff $\alpha^\top x\le\beta$ is valid
-- statement:
--   Let $(w,t)$ be a CSS instance with $w_i\le t-1$ for all $i$ and $t\ge2$, and let $a,b,\alpha,\beta$ be the instance (3)–(6). Then
--   $$
--   \nexists S\subseteq[n]:\ w(S)=t \quad\iff\quad \alpha^\top x\le\beta \text{ is valid for } \operatorname{conv}(\{x\in\{0,1\}^N:a^\top x\le b\}).
--   $$
--
--   This is the co-NP half of the correctness of the reduction in Theorem 4.
--
--   Differences from the source:
--   - encoding: wᵢ ≤ t − 1 for all i ∈ [n] and t ≥ 2 → hypotheses ∀ i, w i + 1 ≤ t and 2 ≤ t, with w : Fin n → ℕ, t : ℕ; reason: the proof's standing assumptions, written without natural-number subtraction
--   - encoding: coordinates x₁, …, x_N → 0-based coordinates: the paper's x_{i+1} is x i : Fin _, and coefficients take i.val + 1; reason: a Lean convention; the same points and the same coefficients
-- source:
--   Chen & Zhu, The Complexity of Recognizing Facets for the Knapsack Polytope, arXiv:2211.03311v3, Theorem 4, proof, (i), p.12 (cases (a)–(d), pp.9–11)

import Definitions.Def_KnapsackFacets_KnapsackPolytope
import Definitions.Def_KnapsackFacets_Reduction

set_option autoImplicit false

namespace KnapsackFacets

/-- **(i), p.12.** "There does not exist S ⊆ [n] such that w(S) = t if and only if inequality
α⊤x ≤ β is valid for the KP defined by a⊤x ≤ b." Chen & Zhu, arXiv:2211.03311v3, Theorem 4,
proof, (i), p.12.

`a, b, α, β` are the reduction instance (3)–(6) built from the CSS instance `(w, t)`, under the
standing assumptions `wᵢ ≤ t − 1` for all `i` and `t ≥ 2` (p.6).

**Formalization Note.** Validity is `IsValid` on the convex hull `KP a b`, equivalent to the
binary-point form the proof uses (p.9). `wᵢ ≤ t − 1` is `w i + 1 ≤ t`. -/
theorem statement_i {n : ℕ} (w : Fin n → ℕ) (t : ℕ) (ht : 2 ≤ t) (hw : ∀ i, w i + 1 ≤ t) :
    (¬ ∃ S : Finset (Fin n), ∑ i ∈ S, w i = t) ↔
      IsValid (redA w t) (redB w t) (redAlpha w t) (redBeta w t : ℤ) := by sorry

end KnapsackFacets
