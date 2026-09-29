-- Prove2me | Theorems.Thm_HighDimStat_Concentration_separately_convex_lipschitz_concentration
-- name    : HighDimStat.Concentration.separately_convex_lipschitz_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-20T04:16:27.595754+00:00
-- url     : https://prove2.me/theorems/0d3a7882-091f-4276-8792-0a12912d9539
-- title:
--   Theorem 3.4 -- separately convex Lipschitz concentration
-- statement:
--   **Theorem 3.4.** Let $\{X_i\}_{i=1}^n$ be independent random variables, each supported on
--   the interval $[a,b]$, and let $f:\mathbb R^n\to\mathbb R$ be separately convex and
--   $L$-Lipschitz with respect to the Euclidean norm. Then, for all $\delta>0$,
--
--   $$
--   \mathbb P[f(X)\ge\mathbb E[f(X)]+\delta] \;\le\; \exp\Big(-\frac{\delta^2}{4L^2(b-a)^2}\Big).
--   $$
--
--   This is the analog, for independent bounded variables, of Theorem 2.26's Gaussian Lipschitz
--   concentration — but with the additional hypothesis of separate convexity, which (unlike the
--   Gaussian case) cannot be eliminated in general. When $f$ is *jointly* convex, a sharper
--   two-sided bound is available (Theorem 3.24, out of this mission's scope — see
--   `description.md`).
--
--   **Formalization Note** This is the recommended goal's own explicit fallback: `BRIEF.md`
--   names Theorem 3.24 as the primary recommendation but explicitly allows substituting Theorem
--   3.4 "if 3.24's dependence on the unnumbered transportation-cost inequality (Eq. 3.73,
--   attributed to Samson) proves too heavy to state faithfully in the time available." That
--   substitution is made here; see `STATUS.md` for the reasoning. Separate convexity and
--   Euclidean-Lipschitzness are both restated locally in this chapter's own sub-namespace, kept
--   exactly as the book states them (separate convexity is not weakened to joint convexity, nor
--   is it dropped).
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 62 (PDF p. 82), Theorem 3.4, Eq. (3.16)

import Mathlib
import Definitions.Def_HighDimStat_Concentration_IsSeparatelyConvex
import Definitions.Def_HighDimStat_Concentration_IsLLipschitz

open MeasureTheory ProbabilityTheory

namespace HighDimStat.Concentration

/-- **Theorem 3.4**, Wainwright, *High-Dimensional Statistics* (2019), p. 62. Let `{Xᵢ}` be
independent random variables, each supported on `[a,b]`, and let `f : ℝⁿ → ℝ` be separately
convex and `L`-Lipschitz with respect to the Euclidean norm. Then for all `δ>0`,
`P[f(X) ≥ E[f(X)]+δ] ≤ exp(-δ²/(4L²(b-a)²))`. -/
theorem separately_convex_lipschitz_concentration {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob] (X : Fin n → Ω → ℝ) (a b : ℝ) (hab : a < b)
    (hIndep : iIndepFun X Prob) (hSupport : ∀ i, ∀ᵐ ω ∂Prob, X i ω ∈ Set.Icc a b)
    (f : (Fin n → ℝ) → ℝ) (L : ℝ) (hSepConvex : IsSeparatelyConvex f) (hLip : IsLLipschitz f L)
    (hInt : Integrable (fun ω => f (fun i => X i ω)) Prob) (δ : ℝ) (hδ : 0 < δ) :
    Prob.real {ω | (∫ ω', f (fun i => X i ω') ∂Prob) + δ ≤ f (fun i => X i ω)} ≤
      Real.exp (-(δ ^ 2) / (4 * L ^ 2 * (b - a) ^ 2)) := by sorry

end HighDimStat.Concentration
