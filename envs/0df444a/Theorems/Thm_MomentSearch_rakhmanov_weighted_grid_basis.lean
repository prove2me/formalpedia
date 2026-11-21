-- Prove2me | Theorems.Thm_MomentSearch_rakhmanov_weighted_grid_basis
-- name    : MomentSearch.rakhmanov_weighted_grid_basis
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-20T23:14:59.073729+00:00
-- url     : https://prove2.me/theorems/2b4664fb-0349-42c0-88f8-1e8f26defae2
-- title:
--   Weighted Lagrange basis bound on the midpoint grid
-- statement:
--   For the $N$ midpoint grid nodes $\zeta_j=-1+(2j-1)/N$, let $L_j$ be the corresponding Lagrange basis polynomial. Write $w(z)=\exp(V_1(z)-N)$, where $V_1$ is the uniform-grid logarithmic potential (2.1). The Lean statement uses its explicit elementary formula. There is an absolute constant $A>0$ with
--   $$
--   |L_j(x)|\le A\frac{w(\zeta_j)}{w(x)}\frac{1}{\max(1,N|\zeta_j-x|)}
--   \qquad(-1\le x\le1).
--   $$
--   Off the nodes, use $L_j(x)=T(x)/((x-\zeta_j)T'(\zeta_j))$, the nodal-product estimate in Lemma 1 and (2.6), and the cosine bound (2.28). At a node, the basis values are given by their interpolation property. The cap is written with a positive denominator so that the expression covers coincidence.
-- source:
--   E. A. Rakhmanov, Bounds for polynomials with a unit discrete norm, Ann. of Math. 165 (2007), 55–88. https://annals.math.princeton.edu/2007/165-1/p03 Lemma 1 and §2.2, (2.6), (2.19)–(2.20), (2.28), pp. 63–67.

import Mathlib

theorem MomentSearch.rakhmanov_weighted_grid_basis :
    ∃ A : ℝ, 0 < A ∧
      ∀ N : ℕ, 0 < N →
      let ζ : ℕ → ℝ := fun j => -1 + (2 * (j : ℝ) - 1) / (N : ℝ)
      let w : ℝ → ℝ := fun z => Real.exp (-(N : ℝ) / 2 *
        ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)))
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ j ∈ Finset.Icc 1 N,
        |(Lagrange.basis (Finset.Icc 1 N) ζ j).eval x| ≤
          A * (w (ζ j) / w x) / max 1 ((N : ℝ) * |ζ j - x|) := by sorry
