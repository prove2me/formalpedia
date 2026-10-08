-- Prove2me | Theorems.Thm_NagaevLD_FukNagaev_eq_1_20
-- name    : NagaevLD.FukNagaev.eq_1_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:58.901518+00:00
-- url     : https://prove2.me/theorems/b70e9a76-0f80-4dcb-a253-c4e0573b62b8
-- title:
--   (1.20), pp. 751–752 — under (1.6) and βx ≥ μ(−∞, Y) or β ≥ tα/2, P(S̃_n ≥ x) < P₅
-- statement:
--   In the setting of (1.19), suppose condition (1.6) holds and, in addition, at least one of
--   $$\beta x\ge\mu(-\infty,Y),\qquad \beta\ge\frac{t\alpha}2$$
--   holds. Then
--   $$P(\tilde S_n\ge x)<P_5=\exp\Big\{\Big(\beta-\frac{t\alpha}2\Big)\frac xy-\Big(\beta\frac xy-\frac{\mu(-\infty,Y)}y\Big)\log\Big(\frac{\beta xy^{t-1}}{A(t;0,Y)}+1\Big)\Big\}.$$
--
--   The page's display (1.20) is the sub-case $h_2\le t/y<h_1$ with $\beta x\ge\mu(-\infty,Y)$ (taking $h=t/y$ in (1.17)); in the sub-case $h_1>h_2>t/y$ it shows $P(\tilde S_n\ge x)<P_4<P_5$, and when $\beta x<\mu(-\infty,Y)$ but $\beta\ge t\alpha/2$ it notes $P_5>1$. The statement here is the summary on p. 752; with (1.8) it gives (1.7a).
--
--   **Formalization Note** (1.6) is `cond_1_6` (including $A(t;0,Y)>0$). Finiteness of $B^2(-\infty,Y)$ is assumed summand by summand.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), pp. 751–752, proof of Theorem 1.3, (1.20) and the summary after it

import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem eq_1_20 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (y : ℝ) (hy0 : 0 < y) (hyy : ∀ i, yv i ≤ y)
    (t : ℝ) (ht : 2 ≤ t)
    (α β : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hβ : β = 1 - α)
    (hL2 : ∀ i, IntegrableOn (fun ω => X i ω ^ 2) {ω | X i ω ≤ yv i} P)
    (h16 : cond_1_6 t α β x y (B2Y P X yv) (AY P X yv t))
    (hextra : β * x ≥ muY P X yv ∨ β ≥ t * α / 2) :
    P.real {ω | x ≤ St X yv ω} < P5 t α β x y (muY P X yv) (AY P X yv t) := by sorry

end NagaevLD.FukNagaev
