-- Prove2me | Theorems.Thm_HighDimCLT_Hyperrect_lemma_5_1
-- name    : HighDimCLT.Hyperrect.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:05.943976+00:00
-- url     : https://prove2.me/theorems/4abd7bcf-ee5d-4830-aef6-6992d198eca5
-- title:
--   Lemma 5.1 (Key lemma), p. 2322 — ϱ_n ≲ (φ² log²p/n^{1/2}){φL_nϱ_n + L_n log^{1/2}p + φM_n(φ)} + log^{1/2}p/φ
-- statement:
--   This is the key lemma behind the high-dimensional CLT for hyperrectangles.
--
--   Let $n \ge 4$, $p \ge 3$, and let $X_1, \dots, X_n$ be independent centred random vectors in $\mathbb R^p$ with $\mathrm E[X_{ij}^2] < \infty$ and $\mathrm E|X_{ij}|^3 < \infty$. Let $Y_1, \dots, Y_n$ be independent with $Y_i \sim N(0, \mathrm E[X_iX_i'])$, and assume moreover that the $Y$'s are independent of the $X$'s. Let $S^X_n, S^Y_n$ be the normalized sums, $L_n$ and $M_n(\phi)$ the moment quantities, and
--
--   $$\varrho_n := \sup_{y \in \mathbb R^p,\ v \in [0,1]} \big|\mathrm P(\sqrt v S^X_n + \sqrt{1-v} S^Y_n \le y) - \mathrm P(S^Y_n \le y)\big|.$$
--
--   For every $b > 0$ there is a constant $K > 0$, depending only on $b$, such that whenever $n^{-1}\sum_{i=1}^n \mathrm E[X_{ij}^2] \ge b$ for all $j = 1, \dots, p$, then for every $\phi \ge 1$,
--
--   $$\varrho_n \le K\left[\frac{\phi^2\log^2 p}{n^{1/2}}\Big\{\phi L_n\varrho_n + L_n\log^{1/2}p + \phi M_n(\phi)\Big\} + \frac{\log^{1/2}p}{\phi}\right].$$
--
--   The inequality is recursive in $\varrho_n$; Corollary 5.1, its hyperrectangle version, is solved for $\varrho'_n$ in the proof of Theorem 2.1.
--
--   **Formalization Note** The paper's "$\lesssim$ up to a constant $K$ that depends only on $b$" is the existential $K$, quantified after $b$ and before $n$, $p$, the probability space and every random vector. Joint independence of $(X_1, \dots, X_n, Y_1, \dots, Y_n)$ is part of the page's definition of $\varrho_n$. The hypothesis $\mathrm E|X_{ij}|^3 < \infty$ is added: if some third moment were infinite, $L_n = \infty$ and the page's right-hand side would be $+\infty$, so nothing is lost. The Gaussian law is Mathlib's `multivariateGaussian 0 Σ` with $\Sigma = \mathrm E[X_iX_i']$, which is positive semidefinite.
-- source:
--   Chernozhukov, Chetverikov and Kato, Central limit theorems and bootstrap in high dimensions, Ann. Probab. 45 (2017), p. 2322, §5, Lemma 5.1 and the definition of ϱ_n; standing setting §1, p. 2309, §1.1, p. 2312

import Mathlib
import Definitions.Def_HighDimCLT_Hyperrect_Setting

open MeasureTheory ProbabilityTheory

namespace HighDimCLT.Hyperrect

universe u

theorem lemma_5_1 :
    ∀ b : ℝ, 0 < b → ∃ K : ℝ, 0 < K ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (n p : ℕ), 4 ≤ n → 3 ≤ p →
      ∀ (X Y : Fin n → Ω → E p)
        (hXm : ∀ i, Measurable (X i)) (hXind : iIndepFun X P)
        (hX0 : ∀ i j, ∫ ω, X i ω j ∂P = 0)
        (hX2 : ∀ i j, MemLp (fun ω => X i ω j) 2 P)
        (hX3 : ∀ i j, Integrable (fun ω => |X i ω j| ^ 3) P)
        (hYm : ∀ i, Measurable (Y i)) (hYind : iIndepFun Y P)
        (hYlaw : ∀ i, P.map (Y i) = multivariateGaussian 0 (covMat P (X i)))
        (hXYind : iIndepFun (Sum.elim X Y) P)
        (hb : ∀ j, b ≤ (∑ i, ∫ ω, X i ω j ^ 2 ∂P) / n),
      ∀ φ : ℝ, 1 ≤ φ →
        varrho P X Y ≤ K * (φ ^ 2 * Real.log p ^ 2 / Real.sqrt n *
            (φ * Ln P X * varrho P X Y + Ln P X * Real.sqrt (Real.log p) + φ * Mn P X Y φ)
          + Real.sqrt (Real.log p) / φ) := by sorry

end HighDimCLT.Hyperrect
