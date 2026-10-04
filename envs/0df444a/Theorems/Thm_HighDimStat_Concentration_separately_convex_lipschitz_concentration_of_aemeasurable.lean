-- Prove2me | Theorems.Thm_HighDimStat_Concentration_separately_convex_lipschitz_concentration_of_aemeasurable
-- name    : HighDimStat.Concentration.separately_convex_lipschitz_concentration_of_aemeasurable
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-02T21:32:57.89726+00:00
-- url     : https://prove2.me/theorems/f705014f-03d5-47c9-aa08-8314abe9028b
-- title:
--   Separately convex Lipschitz concentration for independent measurable bounded coordinates
-- statement:
--   Let $X_1,\ldots,X_n$ be independent, almost-everywhere measurable real random variables on a probability space, each supported almost surely in $[a,b]$, where $a<b$. Let $f:\mathbb R^n\to\mathbb R$ be separately convex and $L$-Lipschitz for the Euclidean norm, and suppose $f(X)$ is integrable. For every $\delta>0$,
--
--   $$\mathbb P\{f(X)\ge\mathbb E[f(X)]+\delta\}\le \exp\!\left(-\frac{\delta^2}{4L^2(b-a)^2}\right).$$
--
--   This formulation states coordinate almost-everywhere measurability explicitly. It is the usual random-variable version of Wainwright’s Theorem 3.4. The existing platform theorem `HighDimStat.Concentration.separately_convex_lipschitz_concentration` omits that hypothesis; this separate theorem does not assert that the hypothesis follows from the original statement or that the original statement is false.
-- source:
--   Wainwright, High-Dimensional Statistics (CUP, 2019), Theorem 3.4, printed p. 62; proof in Section 3.1.4, printed pp. 64–67. Explicitly states the measurability required by the usual random-variable formulation. https://anthonyhongxiao.github.io/pdfs/HDS-book.pdf

import Mathlib
import Definitions.Def_HighDimStat_Concentration_IsSeparatelyConvex
import Definitions.Def_HighDimStat_Concentration_IsLLipschitz

open MeasureTheory ProbabilityTheory

namespace HighDimStat.Concentration

theorem separately_convex_lipschitz_concentration_of_aemeasurable
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (X : Fin n → Ω → ℝ) (hXm : ∀ i, AEMeasurable (X i) Prob)
    (a b : ℝ) (hab : a < b) (hIndep : iIndepFun X Prob)
    (hSupport : ∀ i, ∀ᵐ ω ∂Prob, X i ω ∈ Set.Icc a b)
    (f : (Fin n → ℝ) → ℝ) (L : ℝ)
    (hSepConvex : IsSeparatelyConvex f) (hLip : IsLLipschitz f L)
    (hInt : Integrable (fun ω => f (fun i => X i ω)) Prob)
    (δ : ℝ) (hδ : 0 < δ) :
    Prob.real {ω | (∫ ω', f (fun i => X i ω') ∂Prob) + δ ≤ f (fun i => X i ω)} ≤
      Real.exp (-(δ ^ 2) / (4 * L ^ 2 * (b - a) ^ 2)) := by sorry

end HighDimStat.Concentration
