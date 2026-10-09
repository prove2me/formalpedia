-- Prove2me | Theorems.Thm_LearnNoConc_ERM_betaStar_eq_betaN
-- name    : LearnNoConc.ERM.betaStar_eq_betaN
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:47:59.578069+00:00
-- url     : https://prove2.me/theorems/3ce215f4-eeef-4b47-8bc4-14d23902d09a
-- title:
--   §5, p. 20 — β*_N(γ) = β_N(F − f*, γ)
-- statement:
--   Let $(\Omega,\mu)$ be a probability space, $F$ a class of real functions on $\Omega$, $f^*:\Omega\to\mathbb R$, $N\ge1$ and $\gamma>0$. Then the parameter of Definition 2.1 equals the parameter of Definition 5.2 for the shifted class $F-f^*=\{f-f^*:f\in F\}$:
--
--   $$\beta^*_N(\gamma)=\beta_N(F-f^*,\gamma).$$
--
--   The two definitions differ only in normalization ($1/\sqrt N$ with the bound $\gamma\sqrt N r$, versus $1/N$ with the bound $\gamma r$) and in the centre of the ball. The identity transfers the results proved for general classes $H$ in §5 to the parameter $\beta^*_N$ that appears in Theorem 3.1.
--
--   **Formalization Note** Both sides are $[0,\infty]$-valued infima, with expectations of suprema taken in $[0,\infty]$.
-- source:
--   Mendelson, Learning without Concentration, arXiv:1401.0304v2, §5, p. 20, "observe that β*_N(γ) = β_N(F − f*, γ)"

import Mathlib
import Definitions.Def_LearnNoConc_ERM_Setting

namespace LearnNoConc.ERM

open MeasureTheory
open scoped ENNReal

/-- §5, p. 20: `β*_N(γ) = β_N(F − f*, γ)`. -/
theorem betaStar_eq_betaN {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Set (Ω → ℝ)) (fstar : Ω → ℝ) (N : ℕ) (hN : 0 < N)
    (γ : ℝ) (hγ : 0 < γ) :
    betaStar μ F fstar N γ = betaN μ (shift F fstar) N γ := by sorry

end LearnNoConc.ERM
