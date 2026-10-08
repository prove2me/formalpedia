-- Prove2me | Theorems.Thm_NagaevLD_FukNagaev_p4_case
-- name    : NagaevLD.FukNagaev.p4_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:35.43672+00:00
-- url     : https://prove2.me/theorems/0e0a40aa-f148-4f44-8c24-60752a7fc320
-- title:
--   pp. 751–752 — under (1.6), P(S̃_n ≥ x) < P₄
-- statement:
--   In the setting of (1.19), suppose instead that condition (1.6) holds:
--   $$\max\Big[t,\ \log\Big(\frac{\beta xy^{t-1}}{A(t;0,Y)}+1\Big)\Big]<\frac{\alpha xy}{e^tB^2(-\infty,Y)}.$$
--   Then
--   $$P(\tilde S_n\ge x)<P_4=\exp\Big\{\beta\frac xy-\Big(\big(1-\tfrac\alpha2\big)\frac xy-\frac{\mu(-\infty,Y)}y\Big)\log\Big(\frac{\beta xy^{t-1}}{A(t;0,Y)}+1\Big)\Big\}.$$
--
--   This is the polynomial-type bound for the truncated sum; with (1.8) it gives (1.7). The page proves it in the two sub-cases $h_1>h_2>t/y$ (taking $h=h_2$ in (1.18)) and $h_2\le t/y<h_1$ (taking $h=h_2$ in (1.17)).
--
--   **Formalization Note** Condition (1.6) is `cond_1_6`, which requires $A(t;0,Y)>0$, as the page's (1.6) does implicitly (for $A=0$ its left side is $+\infty$). Finiteness of $B^2(-\infty,Y)$ is assumed summand by summand.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), pp. 751–752, proof of Theorem 1.3, case h₁ > max[t/y, h₂]

import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem p4_case {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (y : ℝ) (hy0 : 0 < y) (hyy : ∀ i, yv i ≤ y)
    (t : ℝ) (ht : 2 ≤ t)
    (α β : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hβ : β = 1 - α)
    (hL2 : ∀ i, IntegrableOn (fun ω => X i ω ^ 2) {ω | X i ω ≤ yv i} P)
    (h16 : cond_1_6 t α β x y (B2Y P X yv) (AY P X yv t)) :
    P.real {ω | x ≤ St X yv ω} < P4 t α β x y (muY P X yv) (AY P X yv t) := by sorry

end NagaevLD.FukNagaev
