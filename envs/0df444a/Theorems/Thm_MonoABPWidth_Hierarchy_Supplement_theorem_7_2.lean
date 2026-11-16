-- Prove2me | Theorems.Thm_MonoABPWidth_Hierarchy_Supplement_theorem_7_2
-- name    : MonoABPWidth.Hierarchy.Supplement.theorem_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:38:00.930356+00:00
-- url     : https://prove2.me/theorems/99a53031-6084-4f17-8698-ebf5e24f15cc
-- title:
--   Theorem 7.2 (corrected: positive degree) — compatible-weight lower bound
-- statement:
--   Let $p$ be a monotone real polynomial of positive degree $n$, with any compatible weight $w$ and growth function $G$ from §7. Let $L:\mathbb N\times\mathbb N\to[0,+\infty]$ satisfy both
--   $$L(1,d)\le G(1)\quad(d\ge0),$$
--   $$L\left(\sum_{i=1}^{\ell}n_i,d\right)\le \frac{G(\sum_i n_i)}{\prod_iG(n_i)}\sum_iL(n_i,d-1)\quad(d,\ell,n_i\ge1).$$
--   Every arbitrary-fan-in monotone formula $F$ computing $p$ then satisfies
--   $$\lambda(F)\ge L(n,d_\times(F)).$$
--   Depth zero and infinite lower bounds remain allowed. Growth bounds concern relevant polynomials, and relevance means $p=qa+b$ with monotone $q,a,b$. This is the generic lower-bound framework, not a specialization to support cardinality or the permanent recurrence.
--
--   Differences from the source:
--   - correction: degree n without an explicit positive-degree qualification → 1 ≤ totalDegree p; reason: the proof treats n=1 and n>1 only; for p=1, w=G=1, L(0,d)=2 and L(n,d)=0 for n>0 satisfy both source inequalities but the one-leaf constant formula violates the claimed bound
--   - reading: growth is first described for all polynomials, then for relevant polynomials in §7 → growth bounds on relevant monotone polynomials and weight axioms on monotone polynomials; reason: uses the explicit relevance-based context of the framework rather than a bound on unrelated polynomials
--   - encoding: a lower-bound function that may take infinity → an arbitrary ENNReal-valued nonnegative lower-bound function; reason: negative lower bounds are trivial; their positive parts satisfy the same inequalities, while +infinity must remain representable
--   - generalization: bounded-depth formulas are assumed alternating without loss of generality in §2.3 → the universal lower bound also ranges over nonalternating trees; reason: contracting consecutive gates preserves leaves and never increases multiplication depth; the displayed bound is nonincreasing in depth
--   - generalization: a polynomial in a finite set of variables → any ambient variable type with finitely supported polynomials and finite formula trees; reason: each polynomial and formula uses finitely many variables; restricting the weight and growth data to those variables recovers the finite-variable source setting
-- source:
--   Julian Dörfler, Alexander Rogovskyy, STOC 2027 submission #927 (October 2026), Theorem 7.2, p.20, PDF21

import Definitions.Def_MonoABPWidth_Hierarchy_Supplement_weights

open scoped BigOperators ENNReal

namespace MonoABPWidth.Hierarchy.Supplement

/-- Theorem 7.2, p.20 (PDF21), with both (7.3) and (7.4) and arbitrary
compatible weight/growth/lower-bound functions. Positive degree is the domain of
the lower-bound argument. Depth zero remains allowed. -/
theorem theorem_7_2 {σ : Type} (p : MvPolynomial σ ℝ)
    (hp : MonotonePolynomial p) (hn : 1 ≤ p.totalDegree)
    (w : PolynomialWeight σ) (Gr : ℕ → NNReal)
    (hc : Compatible p w Gr) (L : ℕ → ℕ → ℝ≥0∞)
    (hL : LowerBoundConditions Gr L) (F : Formula σ) (hF : F.eval = p) :
    L p.totalDegree F.mulDepth ≤ (F.leaves : ℝ≥0∞) := by sorry

end MonoABPWidth.Hierarchy.Supplement
