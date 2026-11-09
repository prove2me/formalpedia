-- Prove2me | Theorems.Thm_NAMatchEst_proposition_2_1
-- name    : NAMatchEst.proposition_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:52:36.499028+00:00
-- url     : https://prove2.me/theorems/d7e63bf5-f97c-4ecf-be5a-ffa02ca19c68
-- title:
--   Proposition 2.1 — Chernoff bound with bracketing means
-- statement:
--   Let $X_1,\dots,X_m$ be independent random variables on a probability space, each with range $[0,1]$, and let $X:=\sum_{i=1}^m X_i$. Let $\lambda_L,\lambda_H$ be reals with $\lambda_L\le\mathbb E[X]\le\lambda_H$. Then for every $\varepsilon>0$,
--
--   $$
--   \Pr\big(X\ge(1+\varepsilon)\lambda_H\big)\le\exp\Big(-\frac{\varepsilon^2\lambda_H}{3+\varepsilon}\Big)
--   \quad\text{and}\quad
--   \Pr\big(X\le(1-\varepsilon)\lambda_L\big)\le\exp\Big(-\frac{\varepsilon^2\lambda_L}{2+\varepsilon}\Big).
--   $$
--
--   This is the concentration inequality behind every test of Section 3 (through its consequences (5)). The bracketing means $\lambda_L,\lambda_H$ let it be applied when only bounds on $\mathbb E[X]$ are known.
--
--   **Formalization Note** The variables are measurable real functions, mutually independent, with values in $[0,1]$ at every point. No sign is assumed on $\lambda_L$.
--
--   Differences from the source:
--   - encoding: independent random variables with range [0,1] → measurable X i : Ω → ℝ, iIndepFun, X i ω ∈ [0,1] for every ω; reason: Lean convention; same instances
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Proposition 2.1, p.13 (PDF 17)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace NAMatchEst

/-- **Proposition 2.1 (Chernoff bound).** Let `X₁, …, X_m` be independent random variables with
range `[0, 1]`, `X := Σ X_i`, and `λ_L ⩽ E[X] ⩽ λ_H`. Then for every `ε > 0`,
`Pr(X ⩾ (1 + ε)λ_H) ⩽ exp(−ε²λ_H/(3 + ε))` and `Pr(X ⩽ (1 − ε)λ_L) ⩽ exp(−ε²λ_L/(2 + ε))`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Proposition 2.1, p.13 (PDF 17).

**Formalization Note** The variables are measurable real functions on a probability space, mutually
independent (`iIndepFun`) and valued in `[0, 1]` at every point; they are therefore integrable, so
`E[X]` is a genuine Bochner integral. `λ_L`, `λ_H` are arbitrary reals with the stated bracket
(no positivity is assumed; for `λ_L ⩽ 0` the lower-tail bound is at least 1). -/
theorem proposition_2_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (X : Fin m → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hrange : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) (lamL lamH : ℝ)
    (hL : lamL ≤ ∫ ω, ∑ i, X i ω ∂P) (hH : ∫ ω, ∑ i, X i ω ∂P ≤ lamH) (ε : ℝ) (hε : 0 < ε) :
    P.real {ω | (1 + ε) * lamH ≤ ∑ i, X i ω} ≤ Real.exp (-(ε ^ 2 * lamH) / (3 + ε)) ∧
      P.real {ω | ∑ i, X i ω ≤ (1 - ε) * lamL} ≤ Real.exp (-(ε ^ 2 * lamL) / (2 + ε)) := by sorry

end NAMatchEst
