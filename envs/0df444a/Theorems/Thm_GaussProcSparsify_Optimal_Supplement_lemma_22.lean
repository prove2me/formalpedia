-- Prove2me | Theorems.Thm_GaussProcSparsify_Optimal_Supplement_lemma_22
-- name    : GaussProcSparsify.Optimal.Supplement.lemma_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:25:08.656205+00:00
-- url     : https://prove2.me/theorems/32804803-5edf-4529-9fca-7c14727b33af
-- title:
--   Lemma 22 — Zamir–Feder entropy inequality
-- statement:
--   Let $\mu$ be a probability law on $\mathbb R$ with a Lebesgue density and finite differential entropy $h$, and let $x$ have the product law $\mu^{\otimes n}$. For every real $d\times n$ matrix $M$ with orthonormal rows, $MM^\top=I_d$, its image has a well-defined extended differential entropy $H$ and
--   $$H=h(Mx)\ge d\,h.$$
--   The projected entropy may equal $+\infty$; the common coordinate entropy is finite. No variance, bounded support, log-concavity or Gaussian hypothesis is imposed. When $d=0$, the projected law has entropy zero. This inequality supports the cube lower bound of Theorem 5.
--
--   Differences from the source:
--   - encoding: Euclidean R^n → EuclideanSpace ℝ (Fin n); reason: the fixed Euclidean coordinates, inner product and standard Gaussian law are preserved
--   - encoding: an i.i.d. random vector with finite coordinate differential entropy → a common probability law μ with HasDifferentialEntropy μ h for real h, and the actual product-law pushforward under M; reason: the inequality depends only on the joint law, and the finite entropy witness records the actual signed integral
--   - encoding: differential entropy h(Mx) → an EReal entropy value with a density and well-definedness witness, using the published signed entropy integral; reason: permits infinite positive projected entropy while excluding undefined opposite infinities, with no moment or support restriction
--   - generalization: the source writes the common entropy as h(x₁), presupposing n>0 → also includes the empty product n=0, for which row orthonormality forces d=0; reason: the supplied common law still has finite entropy, while the unique zero-dimensional image has entropy zero, adding only the trivial empty-vector instance
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), Lemma 22, PDF p. 34 (printed p. 33), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Definitions.Def_GaussProcSparsify_Optimal_Supplement_Entropy

open MeasureTheory ProbabilityTheory

namespace GaussProcSparsify.Optimal.Supplement

/-- Lemma 22, PDF p. 34. No variance, support, symmetry or Gaussian restriction.
The projected entropy is well-defined and may be +∞. Row orthonormality is literal. -/
theorem lemma_22 (n d : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : ℝ) (hh : HasDifferentialEntropy μ (h : EReal))
    (M : Matrix (Fin d) (Fin n) ℝ) (hM : M * M.transpose = 1) :
    ∃ H : EReal, HasDifferentialEntropy (iidLinearImage μ M) H ∧
      ((d : ℝ) * h : ℝ) ≤ H := by sorry

end GaussProcSparsify.Optimal.Supplement
