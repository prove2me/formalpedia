-- Prove2me | Theorems.Thm_MaxCutMatrix2027_Upper_hausdorff_moments
-- name    : MaxCutMatrix2027.Upper.hausdorff_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T12:48:07.586423+00:00
-- url     : https://prove2.me/theorems/b662fd67-6e34-4792-8bb4-6a40b9881a72
-- title:
--   Lemma 4.7 — Both Hausdorff-distance moments
-- statement:
--   Let $y_1,\ldots,y_n$ be arbitrary deterministic vectors in a finite-dimensional real Euclidean space, and let $1\le s\le n$ be real. Include vertices independently with probability $s/n$. Define
--   $$K=\left\{n^{-1}\sum_i x_i y_i:x\in[-1,1]^n\right\},\quad
--   K_Q=\left\{s^{-1}\sum_{i\in Q}x_i y_i:x\in[-1,1]^n\right\},\quad
--   \Delta=d_H(K_Q,K),\quad t_y=n^{-1}\sum_i\|y_i\|_2^2.$$
--   Then both moment bounds hold with the stated constants:
--   $$\mathbb E\Delta\le4\sqrt{t_y/s},\qquad \mathbb E\Delta^2\le17t_y/s.$$
--   No length bound on the vectors, positivity of $t_y$, or positive ambient dimension is assumed. The source's retained spectral vectors are particular choices of these vectors. These moments quantify the discrepancy between sampled and population feasible moment sets.
--
--   Differences from the source:
--   - encoding: vertices labelled by [n] and independent Bernoulli selectors → Fin n and the exact finite Bernoulli-subset expectation; reason: relabeling is bijective and the subset weights are exactly the independent-selector law
--   - generalization: the retained spectral vectors constructed on p.21 → arbitrary deterministic vectors in any finite-dimensional real Euclidean space; reason: the moment argument uses only the displayed vector averages and their squared lengths, and includes every source spectral instance
--   - encoding: d_H defined on p.21 as the max of the two sup–inf Euclidean distances between nonempty compact sets → Metric.hausdorffDist in EuclideanSpace; reason: both sets are nonempty and compact (they contain zero and are continuous images of the cube), where Mathlib's value is exactly that max
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), Lemma 4.7, p.22 (PDF p.22); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Definitions.Def_MaxCutMatrix2027_Upper_MatrixModel
set_option autoImplicit false

namespace MaxCutMatrix2027.Upper

/-- Lemma 4.7, p.22. The argument holds for all deterministic Euclidean vectors,
including dimension zero, without spectral or length restrictions. -/
theorem hausdorff_moments (n d : ℕ) (y : Fin n → EuclideanSpace ℝ (Fin d))
    (s : ℝ) (hs : 1 ≤ s) (hsn : s ≤ n) :
    sampleAverage (s / n) (sampleDistance y s) ≤ 4 * Real.sqrt (averageEnergy y / s) ∧
    sampleAverage (s / n) (fun Q => sampleDistance y s Q ^ 2) ≤ 17 * averageEnergy y / s := by sorry

end MaxCutMatrix2027.Upper
