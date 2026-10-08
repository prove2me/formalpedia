-- Prove2me | Theorems.Thm_HighDimCLT_Hyperrect_theorem_2_1
-- name    : HighDimCLT.Hyperrect.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:40:05.049127+00:00
-- url     : https://prove2.me/theorems/99a3469e-5dd6-4e28-ac4b-f8958f94e700
-- title:
--   Theorem 2.1, p. 2313 — ρ_n(𝒜^re) ≤ K₁[(L̄_n² log⁷p/n)^{1/6} + M_n(φ_n)/L̄_n], φ_n = K₂(L̄_n² log⁴p/n)^{−1/6}
-- statement:
--   This is the abstract high-dimensional central limit theorem for hyperrectangles.
--
--   Let $n \ge 4$ and $p \ge 3$. Let $X_1, \dots, X_n$ be independent random vectors in $\mathbb R^p$ with $\mathrm E[X_{ij}] = 0$, $\mathrm E[X_{ij}^2] < \infty$ and $\mathrm E|X_{ij}|^3 < \infty$ for all $i, j$, and let $Y_1, \dots, Y_n$ be independent centred Gaussian vectors with $Y_i \sim N(0, \mathrm E[X_iX_i'])$. Write $S^X_n = n^{-1/2}\sum_i X_i$, $S^Y_n = n^{-1/2}\sum_i Y_i$, $L_n = \max_j n^{-1}\sum_i \mathrm E|X_{ij}|^3$ and $M_n(\phi) = M_{n,X}(\phi) + M_{n,Y}(\phi)$ with
--
--   $$M_{n,X}(\phi) = \frac1n\sum_{i=1}^n \mathrm E\Big[\max_{j}|X_{ij}|^3\,1\Big\{\max_{j}|X_{ij}| > \sqrt n/(4\phi\log p)\Big\}\Big].$$
--
--   For every $b > 0$ there exist constants $K_1, K_2 > 0$, depending only on $b$, such that the following holds. If $n^{-1}\sum_{i=1}^n \mathrm E[X_{ij}^2] \ge b$ for all $j = 1, \dots, p$, then for every constant $\bar L_n \ge L_n$,
--
--   $$\rho_n(\mathcal A^{\mathrm{re}}) := \sup_{A \in \mathcal A^{\mathrm{re}}}\big|\mathrm P(S^X_n \in A) - \mathrm P(S^Y_n \in A)\big| \le K_1\left[\left(\frac{\bar L_n^2\log^7 p}{n}\right)^{1/6} + \frac{M_n(\phi_n)}{\bar L_n}\right], \qquad \phi_n := K_2\left(\frac{\bar L_n^2\log^4 p}{n}\right)^{-1/6},$$
--
--   where $\mathcal A^{\mathrm{re}}$ is the class of all hyperrectangles $\{w : a_j \le w_j \le b_j \ \forall j\}$ with $-\infty \le a_j \le b_j \le \infty$.
--
--   The error bound depends on the dimension only through $\log p$, so the distribution of a sum of independent high-dimensional vectors is close to its Gaussian analogue on hyperrectangles even when $p$ is much larger than $n$; this underlies simultaneous inference on many means.
--
--   **Formalization Note** $K_1, K_2$ are quantified after $b$ and before $n$, $p$, the probability space, the random vectors, $\bar L_n$ and the hyperrectangle. The bound on the supremum is stated for each hyperrectangle, which is equivalent. The hypothesis $\mathrm E|X_{ij}|^3 < \infty$ is added: if some third moment were infinite, $L_n = \infty$, no finite $\bar L_n \ge L_n$ exists and the page's statement is vacuous, so nothing is lost. The variance condition forces $L_n \ge b^{3/2} > 0$, so $\bar L_n > 0$ and $\phi_n > 0$. $M_n$ is evaluated by formula (5) also when $\phi_n < 1$. The $X$'s and $Y$'s need not be independent of each other, since $\rho_n$ depends only on the two laws. The Gaussian law is Mathlib's `multivariateGaussian 0 Σ` with $\Sigma = \mathrm E[X_iX_i']$, which is positive semidefinite.
-- source:
--   Chernozhukov, Chetverikov and Kato, Central limit theorems and bootstrap in high dimensions, Ann. Probab. 45 (2017), p. 2313, Theorem 2.1, displays (6), (7); setting §1, p. 2309, (1) p. 2310, §1.1 and (4), (5), p. 2312

import Mathlib
import Definitions.Def_HighDimCLT_Hyperrect_Setting

open MeasureTheory ProbabilityTheory

namespace HighDimCLT.Hyperrect

universe u

theorem theorem_2_1 :
    ∀ b : ℝ, 0 < b → ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (n p : ℕ), 4 ≤ n → 3 ≤ p →
      ∀ (X Y : Fin n → Ω → E p)
        (hXm : ∀ i, Measurable (X i)) (hXind : iIndepFun X P)
        (hX0 : ∀ i j, ∫ ω, X i ω j ∂P = 0)
        (hX2 : ∀ i j, MemLp (fun ω => X i ω j) 2 P)
        (hX3 : ∀ i j, Integrable (fun ω => |X i ω j| ^ 3) P)
        (hYm : ∀ i, Measurable (Y i)) (hYind : iIndepFun Y P)
        (hYlaw : ∀ i, P.map (Y i) = multivariateGaussian 0 (covMat P (X i)))
        (hb : ∀ j, b ≤ (∑ i, ∫ ω, X i ω j ^ 2 ∂P) / n),
      ∀ Lbar : ℝ, Ln P X ≤ Lbar →
      ∀ lo hi : Fin p → EReal, (∀ j, lo j ≤ hi j) →
        |P.real {ω | normSum X ω ∈ hyperrect lo hi} - P.real {ω | normSum Y ω ∈ hyperrect lo hi}|
          ≤ K₁ * ((Lbar ^ 2 * Real.log p ^ 7 / n) ^ (1 / 6 : ℝ)
              + Mn P X Y (K₂ * (Lbar ^ 2 * Real.log p ^ 4 / n) ^ (-(1 / 6 : ℝ))) / Lbar) := by sorry

end HighDimCLT.Hyperrect
