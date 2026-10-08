-- Prove2me | Theorems.Thm_HighDimCLT_MultBoot_lemma_A_1
-- name    : HighDimCLT.MultBoot.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:40:36.390126+00:00
-- url     : https://prove2.me/theorems/03294218-fdd4-4cbe-869d-646d81b73f01
-- title:
--   Lemma A.1, p. 2323 — Nazarov's inequality P(Y ≤ y + a) − P(Y ≤ y) ≤ Ca√(log p), C depending only on b
-- statement:
--   For every $b>0$ there is a constant $C>0$, depending only on $b$, with the following property. Let $p\ge3$ and let $Y=(Y_1,\dots,Y_p)'$ be a centred Gaussian random vector in $\mathbb R^p$ with $\mathrm E[Y_j^2]\ge b$ for all $j$. Then for every $y\in\mathbb R^p$ and every $a>0$,
--   $$P(Y\le y+a)-P(Y\le y)\le Ca\sqrt{\log p},$$
--   where $Y\le y$ is coordinatewise and $y+a=(y_1+a,\dots,y_p+a)'$.
--
--   This anti-concentration inequality controls how much probability a Gaussian vector puts near the boundary of a lower orthant; it turns smoothing errors into probability errors.
--
--   **Formalization Note** A centred Gaussian vector in $\mathbb R^p$ is represented by its law $N(0,\Sigma)$ (`multivariateGaussian 0 Σ`) with $\Sigma=\mathrm E[YY']$ positive semidefinite and $\Sigma_{jj}=\mathrm E[Y_j^2]\ge b$; every centred Gaussian vector has such a law, so the two forms are equivalent. The constant is chosen after $b$ and before $p$, $\Sigma$, $y$ and $a$.
-- source:
--   Chernozhukov, Chetverikov and Kato, Central limit theorems and bootstrap in high dimensions, Ann. Probab. 45 (2017), p. 2323, App. A, Lemma A.1

import Mathlib
import Definitions.Def_HighDimCLT_MultBoot_Setting

namespace HighDimCLT.MultBoot

open MeasureTheory ProbabilityTheory

universe u

/-- **Lemma A.1 (Nazarov's inequality)**, App. A, p. 2323: there is `C > 0` depending only on
`b` such that for every centred Gaussian vector `Y ∼ N(0, Σ)` in `ℝ^p` (`p ≥ 3`) with
`E[Y_j²] = Σ_jj ≥ b` for all `j`, every `y ∈ ℝ^p` and every `a > 0`,
`P(Y ≤ y + a) − P(Y ≤ y) ≤ C a √(log p)`. A centred Gaussian vector is represented by its law
`multivariateGaussian 0 Σ` with `Σ = E[Y Y′]` positive semidefinite. -/
theorem lemma_A_1 : ∀ b : ℝ, 0 < b → ∃ C : ℝ, 0 < C ∧
    ∀ (p : ℕ), 3 ≤ p → ∀ (S : Matrix (Fin p) (Fin p) ℝ), S.PosSemidef → (∀ j, b ≤ S j j) →
    ∀ (y : EuclideanSpace ℝ (Fin p)) (a : ℝ), 0 < a →
      (multivariateGaussian 0 S).real {w | ∀ j, w j ≤ y j + a}
        - (multivariateGaussian 0 S).real {w | ∀ j, w j ≤ y j}
        ≤ C * a * Real.sqrt (Real.log p) := by sorry

end HighDimCLT.MultBoot
