-- Prove2me | Theorems.Thm_HighDimCLT_Hyperrect_corollary_5_1
-- name    : HighDimCLT.Hyperrect.corollary_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:22.45663+00:00
-- url     : https://prove2.me/theorems/15118cf0-ecfe-4ed3-b453-e8c125297f85
-- title:
--   Corollary 5.1, p. 2323 — ϱ′_n ≲ (φ² log²p/n^{1/2}){φL_nϱ′_n + L_n log^{1/2}p + φM_n(2φ)} + log^{1/2}p/φ
-- statement:
--   This is the hyperrectangle version of the key lemma.
--
--   In the setting of Lemma 5.1 ($n \ge 4$, $p \ge 3$; $X_1, \dots, X_n$ independent, centred, with finite second and third moments; $Y_i \sim N(0, \mathrm E[X_iX_i'])$ independent, and independent of the $X$'s), let $\mathcal A^{\mathrm{re}}$ be the class of all hyperrectangles in $\mathbb R^p$ and
--
--   $$\varrho'_n := \sup_{A \in \mathcal A^{\mathrm{re}},\ v \in [0,1]} \big|\mathrm P(\sqrt v S^X_n + \sqrt{1-v} S^Y_n \in A) - \mathrm P(S^Y_n \in A)\big|.$$
--
--   For every $b > 0$ there is a constant $K' > 0$, depending only on $b$, such that whenever $n^{-1}\sum_{i=1}^n \mathrm E[X_{ij}^2] \ge b$ for all $j$, then for every $\phi \ge 1$,
--
--   $$\varrho'_n \le K'\left[\frac{\phi^2\log^2 p}{n^{1/2}}\Big\{\phi L_n\varrho'_n + L_n\log^{1/2}p + \phi M_n(2\phi)\Big\} + \frac{\log^{1/2}p}{\phi}\right].$$
--
--   Theorem 2.1 follows by applying this inequality with $\phi = \phi_n/2$ and solving for $\varrho'_n \ge \rho_n(\mathcal A^{\mathrm{re}})$.
--
--   **Formalization Note** As in Lemma 5.1: $K'$ is quantified after $b$ and before everything else; joint independence of the $X$'s and $Y$'s is part of the setting of $\varrho'_n$, defined on the page right after $\varrho_n$; the third-moment hypothesis is added and loses nothing.
-- source:
--   Chernozhukov, Chetverikov and Kato, Central limit theorems and bootstrap in high dimensions, Ann. Probab. 45 (2017), p. 2323, §5, Corollary 5.1 and the definition of ϱ′_n

import Mathlib
import Definitions.Def_HighDimCLT_Hyperrect_Setting

open MeasureTheory ProbabilityTheory

namespace HighDimCLT.Hyperrect

universe u

theorem corollary_5_1 :
    ∀ b : ℝ, 0 < b → ∃ K' : ℝ, 0 < K' ∧
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
        varrho' P X Y ≤ K' * (φ ^ 2 * Real.log p ^ 2 / Real.sqrt n *
            (φ * Ln P X * varrho' P X Y + Ln P X * Real.sqrt (Real.log p) + φ * Mn P X Y (2 * φ))
          + Real.sqrt (Real.log p) / φ) := by sorry

end HighDimCLT.Hyperrect
