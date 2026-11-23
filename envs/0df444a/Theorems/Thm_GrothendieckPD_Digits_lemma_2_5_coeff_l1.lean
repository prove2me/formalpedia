-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_lemma_2_5_coeff_l1
-- name    : GrothendieckPD.Digits.lemma_2_5_coeff_l1
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:47:51.777777+00:00
-- url     : https://prove2.me/theorems/0e4077ba-6998-43df-99cf-c1bf7c80ea4a
-- title:
--   Lemma 2.5, pair coefficients: $\sum_m |c_m(f,g)|\le 1$
-- statement:
--   Let $f,g:\mathbb R^n\to\{\pm1\}$ be measurable and write
--   $$c_m(f,g)=\langle\Pi_mf,\Pi_mg\rangle_{L^2(\gamma_n)}$$
--   for their degree-$m$ Hermite coefficients. Then the coefficient sequence is absolutely summable and satisfies
--   $$\sum_{m=0}^{\infty}|c_m(f,g)|\le 1.$$
--   This is the first estimate in Lemma 2.5. In the paper it follows by applying Cauchy–Schwarz first coefficientwise and then to the two square-summable sequences $\|P_mf\|_2$ and $\|P_mg\|_2$, and finally using Parseval with $\|f\|_2=\|g\|_2=1$.
--
--   **Formalization Note** The coefficient `coeff` is the published finite moment-sum definition `GrothendieckLB.pmInner`, equal to the displayed projection inner product by Hermite orthonormality. The statement includes `Summable`, so the infinite sum is the genuine sum of the coefficient sequence.
-- source:
--   Steven Heilman, Chris Jones, Giulio Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf, Lemma 2.5 and its proof, p. 5

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_FiniteGames

namespace GrothendieckPD.Digits

/-- The pair-coefficient estimate in Lemma 2.5 (p. 5): for measurable sign functions
$f,g : \mathbb R^n \to \{\pm 1\}$, the Hermite coefficients $c_m(f,g)$ are absolutely
summable and $\sum_m |c_m(f,g)| \le 1$. -/
theorem lemma_2_5_coeff_l1 :
    ∀ (n : ℕ) (f g : (Fin n → ℝ) → ℝ), GrothendieckLB.IsSignFn f → GrothendieckLB.IsSignFn g →
      Summable (fun m => |coeff m f g|) ∧ ∑' m, |coeff m f g| ≤ 1 := by sorry
