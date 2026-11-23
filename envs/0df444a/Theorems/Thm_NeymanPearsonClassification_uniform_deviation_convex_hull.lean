-- Prove2me | Theorems.Thm_NeymanPearsonClassification_uniform_deviation_convex_hull
-- name    : NeymanPearsonClassification.uniform_deviation_convex_hull
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:41:33.893623+00:00
-- url     : https://prove2.me/theorems/c1248bfb-5ec0-406f-af57-ed3d90094596
-- title:
--   Lemma 6.1: uniform deviation of the empirical process over the convex hull
-- statement:
--   Let $h_1,\dots,h_M:\mathcal X\to[-1,1]$ be measurable, $M\ge2$, let $\varphi:[-1,1]\to\mathbb{R}$ be $L$-Lipschitz with $L>0$, and let $\delta\in(0,1)$. Let $X_1,\dots,X_n$, $n\ge1$, be i.i.d. random variables on $\mathcal X$ with law $P$, and write $P_nf=\frac1n\sum_if(X_i)$ and $Pf=\int f\,dP$. Then, with probability at least $1-\delta$,
--
--   $$\sup_{\lambda\in\Lambda}\big|(P_n-P)(\varphi\circ\mathsf h_\lambda)\big|\le\frac{4\sqrt2\,L}{\sqrt n}\sqrt{\log\Big(\frac{2M}{\delta}\Big)}.$$
--
--   This uniform deviation bound over the convex hull of the base classifiers underlies all the probabilistic statements of the paper.
--
--   **Formalization Note** "With probability at least $1-\delta$" is stated as: the event on which the bound fails for some $\lambda\in\Lambda$ has (outer) probability at most $\delta$.
-- source:
--   Rigollet and Tong, Neyman-Pearson classification, convexity and stochastic constraints, arXiv:1102.5750v1 (2011), Section 6.2, Lemma 6.1, p. 15

import Mathlib
import Definitions.Def_NeymanPearsonClassification_Basic

open MeasureTheory ProbabilityTheory

namespace NeymanPearsonClassification

theorem uniform_deviation_convex_hull {d M n : ℕ} (hM : 2 ≤ M) (hn : 1 ≤ n)
    (h : Fin M → EuclideanSpace ℝ (Fin d) → ℝ) (hh : IsBaseFamily h)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (φ : ℝ → ℝ) (L : ℝ) (hL : 0 < L) (hLip : LipschitzOnWith (Real.toNNReal L) φ (Set.Icc (-1) 1))
    (δ : ℝ) (hδ : δ ∈ Set.Ioo 0 1)
    {Omega : Type*} [MeasurableSpace Omega] (μ : Measure Omega) [IsProbabilityMeasure μ]
    (X : Fin n → Omega → EuclideanSpace ℝ (Fin d)) (hXm : ∀ i, Measurable (X i))
    (hXind : iIndepFun X μ) (hXlaw : ∀ i, μ.map (X i) = P) :
    μ {ω | ¬ ∀ lam ∈ stdSimplex ℝ (Fin M),
      |(∑ i, φ (convComb h lam (X i ω))) / n - ∫ x, φ (convComb h lam x) ∂P| ≤
        4 * Real.sqrt 2 * L / Real.sqrt n * Real.sqrt (Real.log (2 * M / δ))} ≤
      ENNReal.ofReal δ := by sorry

end NeymanPearsonClassification
