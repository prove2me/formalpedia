-- Prove2me | Theorems.Thm_ManipPotential_lemma_6_5_L
-- name    : ManipPotential.lemma_6_5_L
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:50:55.664475+00:00
-- url     : https://prove2.me/theorems/edd5ddd4-794a-4583-a144-ea1aaba2502a
-- title:
--   Lemma 6.5, L-compression
-- statement:
--   Let $m\ge 3$, $\lambda=K+1$, and let $g$ satisfy the axioms of Lemma 6.2. For every nonzero $x\in\mathbb Q^m_{\ge0}$ with $X=\sum_i x_i$, if $g(xL)=c_j$, then
--   $$
--   g\!\left(x_j\ell_j+\frac{X-x_j}{\lambda}\ell_{j+1}\right)=c_j.
--   $$
--   This is the L-compression half of Lemma 6.5. It isolates exactly the finite sequence of replacements of $\ell_h$ by $\ell_{j+1}$ used in the paper.
--
--   **Formalization Note** As in the parent target, $g$ is total but its axioms quantify only over nonnegative rational profiles.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.5 (L-Compression), pp.28–29

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_cycL

/-- The L-compression half of Lemma 6.5 (Berker–Conitzer–Hartman–Liu–Oesterheld, arXiv:2602.22838, Lemma 6.5, pp.28–29): every L-profile can be compressed, without changing its winner, into a binary L-profile supported at the winning index and its successor. -/
theorem ManipPotential.lemma_6_5_L {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m)
    (hg : GAxioms K g) (x : Fin m → ℚ) (hx : 0 ≤ x) (hx0 : x ≠ 0) (j : Fin m)
    (hj : g (cycL x) = j) :
    g (x j • unitVec (ell j) +
      (((∑ i, x i) - x j) / ((K : ℚ) + 1)) • unitVec (ell (j + 1))) = j := by sorry
