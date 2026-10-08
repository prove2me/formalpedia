-- Prove2me | Theorems.Thm_NagaevLD_GenMoment_eq_2_46
-- name    : NagaevLD.GenMoment.eq_2_46
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:31.316998+00:00
-- url     : https://prove2.me/theorems/623ac2e8-9a45-4cee-948b-45757981a597
-- title:
--   (2.46), p. 767 — Ee^{hX_j} ≤ ∫_{u<0} e^{hu} dF_j(u) + b_gj sup_{u≥0} e^{hu−g(u)}
-- statement:
--   Let $X_j$ be a real random variable with distribution function $F_j$, let $g:\mathbb R\to\mathbb R$, and let $b_{gj}=E[e^{g(X_j)};X_j\ge 0]$ be finite. For $h\ge0$, let $M$ be any upper bound of $e^{hu-g(u)}$ over $u\ge 0$, for example
--   $$M=\sup_{u\ge 0}e^{hu-g(u)}$$
--   when this supremum is finite. Then
--   $$Ee^{hX_j}=\int_{u<0}e^{hu}\,dF_j(u)+\int_{u\ge0}e^{hu-g(u)}e^{g(u)}\,dF_j(u)
--   \le \int_{u<0}e^{hu}\,dF_j(u)+b_{gj}\,M .$$
--
--   The bound comes from splitting the expectation at $0$ and writing $e^{hu}=e^{hu-g(u)}e^{g(u)}$ on $u\ge 0$. In the proof of Theorem 2.5 it is used with $h=g'(x/n)$, for which the supremum is computed in (2.47).
--
--   **Formalization Note** The paper's supremum is a real supremum, which Lean would evaluate to $0$ when it is infinite; the statement is therefore quantified over every upper bound $M$, which is equivalent when the supremum is finite. The integrability of $e^{g(X_j)}$ on $\{X_j\ge 0\}$ (finiteness of $b_{gj}$) is assumed explicitly. The proof uses $h=g'(x/n)>0$; allowing $h\ge0$ keeps the negative part integrable, so both the displayed equality and inequality represent finite expectations. The statement does not need independence or any other property of $g$.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 767, proof of Theorem 2.5, (2.46)

import Mathlib
import Definitions.Def_NagaevLD_GenMoment_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.GenMoment

/-- (2.46), p. 767: splitting `E e^{h X_j}` at `0` and bounding the part on `X_j ≥ 0` by
`b_gj` times any upper bound `M` of `e^{hu - g(u)}` over `u ≥ 0` (the supremum of the page).
The nonnegative tilt is the one used in the proof of Theorem 2.5. -/
theorem eq_2_46 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hXm : ∀ j, Measurable (X j)) (g : ℝ → ℝ) (j : Fin n)
    (hbg : IntegrableOn (fun ω => Real.exp (g (X j ω))) {ω | 0 ≤ X j ω} P)
    (h M : ℝ) (hh : 0 ≤ h) (hM : ∀ u : ℝ, 0 ≤ u → Real.exp (h * u - g u) ≤ M) :
    (∫ ω, Real.exp (h * X j ω) ∂P) =
        (∫ ω in {ω | X j ω < 0}, Real.exp (h * X j ω) ∂P) +
          (∫ ω in {ω | 0 ≤ X j ω},
            Real.exp (h * X j ω - g (X j ω)) * Real.exp (g (X j ω)) ∂P) ∧
      (∫ ω, Real.exp (h * X j ω) ∂P)
        ≤ (∫ ω in {ω | X j ω < 0}, Real.exp (h * X j ω) ∂P) + bg P X g j * M := by sorry

end NagaevLD.GenMoment
