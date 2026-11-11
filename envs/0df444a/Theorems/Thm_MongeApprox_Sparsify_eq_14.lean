-- Prove2me | Theorems.Thm_MongeApprox_Sparsify_eq_14
-- name    : MongeApprox.Sparsify.eq_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:02:19.758535+00:00
-- url     : https://prove2.me/theorems/953b3855-9667-4d94-b10d-3b6546d534c9
-- title:
--   (14) — replacing on disjoint rectangles moves each quadrant mass by at most one rectangle's mass
-- statement:
--   Let $\mu\ge0$ be finitely supported, let $R_1,\dots,R_k$ be disjoint rectangles, and replace the restriction of $\mu$ to each rectangle $R_t$ of positive mass according to Lemma 7.5 (by any $\nu_t$ with the properties of Lemma 7.5 for $\mu|_{R_t}$). The resulting matrix $\widehat\mu$ has the same row and column sums as $\mu$. A point $(i,j)$ lies strictly inside at most one of the rectangles. Hence, for all integers $i$ and $j$, $\widehat\mu(Q_{ij})=\mu(Q_{ij})$ if $(i,j)$ lies strictly inside none of the rectangles, and $\mu(Q_{ij})\le\widehat\mu(Q_{ij})\le\mu(Q_{ij})+\mu(R_t)$ if $(i,j)$ lies strictly inside $R_t$.
--
--   Differences from the source:
--   - generalization: replace the restriction of µ to each R_t of positive mass according to Lemma 7.5 → any family ν_t, each satisfying Lemma 7.5's conclusion (`IsRectReplacement`) for µ restricted to R_t; reason: the statement holds for every replacement Lemma 7.5 provides, in particular for the one the paper picks
--   - encoding: µ a nonnegative matrix; R_1, …, R_k disjoint rectangles → µ : ℤ × ℤ → ℝ nonnegative with finite support; R : Fin k → Rect pairwise disjoint as sets of positions; reason: a matrix is its finitely supported extension by zero; same instances
-- source:
--   Gorbachev 2026, Edit Distance Approximation: Subquadratic Factor Three and Monge Approximation Schemes (PDF sha256 b7eeb435…), (14) and the two sentences before it, printed p. 36 (PDF 38)

import Mathlib
import Definitions.Def_MongeApprox_Sparsify_Quadrant

namespace MongeApprox.Sparsify

open Classical in
/-- (14): let `R_1, …, R_k` be disjoint rectangles and replace the restriction of a nonnegative,
finitely supported `µ` to each `R_t` of positive mass by any replacement `ν_t` given by Lemma 7.5.
The resulting `µ̂` has the same row and column sums as `µ`; a point lies strictly inside at most
one rectangle; and for all integers `i, j`, `µ̂(Q_ij) = µ(Q_ij)` if `(i, j)` lies strictly inside
none of the rectangles, and `µ(Q_ij) ≤ µ̂(Q_ij) ≤ µ(Q_ij) + µ(R_t)` if it lies strictly inside
`R_t`. -/
theorem eq_14 (μ : ℤ × ℤ → ℝ) (hμ : ∀ z, 0 ≤ μ z) (hfin : (Function.support μ).Finite)
    {k : ℕ} (R : Fin k → Rect)
    (hdisj : ∀ t t', t ≠ t' → Disjoint (R t).toSet (R t').toSet)
    (ν : Fin k → ℤ × ℤ → ℝ)
    (hν : ∀ t, 0 < mass μ (R t).toSet → IsRectReplacement ((R t).restrict μ) (R t) (ν t)) :
    let μhat : ℤ × ℤ → ℝ := fun z =>
      (if ∃ t, 0 < mass μ (R t).toSet ∧ z ∈ (R t).toSet then 0 else μ z) +
        ∑ t, (if 0 < mass μ (R t).toSet then ν t z else 0)
    (∀ a, rowSum μhat a = rowSum μ a) ∧ (∀ b, colSum μhat b = colSum μ b) ∧
    (∀ (i j : ℤ) (t t' : Fin k), StrictlyInside i j (R t) → StrictlyInside i j (R t') → t = t') ∧
    ∀ i j : ℤ,
      ((∀ t, ¬ StrictlyInside i j (R t)) → mass μhat (Q i j) = mass μ (Q i j)) ∧
      (∀ t, StrictlyInside i j (R t) →
        mass μ (Q i j) ≤ mass μhat (Q i j) ∧
          mass μhat (Q i j) ≤ mass μ (Q i j) + mass μ (R t).toSet) := by sorry

end MongeApprox.Sparsify
