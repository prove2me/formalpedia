-- Prove2me | Theorems.Thm_LocalPF_Block_lemma_4_3
-- name    : LocalPF.Block.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:30.914003+00:00
-- url     : https://prove2.me/theorems/230427d9-529c-4eca-ab4d-f369f817ea1f
-- title:
--   Lemma 4.3, pp. 33–34 — exponentially weighted row sums of D = Σ Cⁿ are at most 1/(1 − c)
-- statement:
--   Let $I$ be a finite set, $m$ a pseudometric on $I$ (real valued, $m(i,i)=0$, symmetric, satisfying the triangle inequality), and $C=(C_{ij})_{i,j\in I}$ a matrix with nonnegative entries such that
--   $$\max_{i\in I}\sum_{j\in I}e^{m(i,j)}C_{ij}\le c<1.$$
--   Then the series $D=\sum_{n\ge0}C^n$ converges, and
--   $$\max_{i\in I}\sum_{j\in I}e^{m(i,j)}D_{ij}\le\frac1{1-c}.$$
--   In particular, for every nonempty $J\subseteq I$ and every $i$,
--   $$\sum_{j\in J}D_{ij}\le\frac{e^{-m(i,J)}}{1-c},\qquad m(i,J)=\min_{j\in J}m(i,j).$$
--
--   The lemma turns exponential decay of Dobrushin's matrix $C$ into exponential decay of $D$, which is how decay of correlations enters the comparison theorem.
--
--   **Formalization Note** Convergence of $\sum_n C^n$ is part of the conclusion (as the existence of $D$ with `HasSum`). The case $J=\varnothing$ of the last bound is trivial ($0\le\cdot$) and is omitted.
-- source:
--   Rebeschini & van Handel, Can Local Particle Filters Beat the Curse of Dimensionality?, arXiv:1301.6585v2 (reprint of Ann. Appl. Probab. 25(5), 2015), pp. 33–34, Lemma 4.3

import Mathlib
import Definitions.Def_LocalPF_Block_Setting

open MeasureTheory
open scoped ENNReal

namespace LocalPF.Block

/-- Lemma 4.3 (pp. 33–34). -/
theorem lemma_4_3 {I : Type*} [Fintype I] [DecidableEq I] (m : I → I → ℝ) (hm_self : ∀ i, m i i = 0)
    (hm_symm : ∀ i j, m i j = m j i) (hm_triangle : ∀ i j k, m i k ≤ m i j + m j k)
    (C : Matrix I I ℝ) (hC : ∀ i j, 0 ≤ C i j) (c : ℝ) (hc : c < 1)
    (hCc : ∀ i, ∑ j, Real.exp (m i j) * C i j ≤ c) :
    ∃ D : Matrix I I ℝ, HasSum (fun n : ℕ => C ^ n) D ∧
      (∀ i, ∑ j, Real.exp (m i j) * D i j ≤ 1 / (1 - c)) ∧
      ∀ (i : I) (J : Finset I) (hJ : J.Nonempty),
        ∑ j ∈ J, D i j ≤ Real.exp (-(J.inf' hJ (m i))) / (1 - c) := by sorry

end LocalPF.Block
