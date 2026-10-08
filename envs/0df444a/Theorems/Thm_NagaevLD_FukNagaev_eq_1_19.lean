-- Prove2me | Theorems.Thm_NagaevLD_FukNagaev_eq_1_19
-- name    : NagaevLD.FukNagaev.eq_1_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:38.472273+00:00
-- url     : https://prove2.me/theorems/fa79d738-98c9-4051-81cb-6fad276fd28d
-- title:
--   (1.19), p. 751 — under (1.4), P(S̃_n ≥ x) ≤ P₆
-- statement:
--   Let $X_1,\dots,X_n$ be independent random variables, $x>0$, $y_1,\dots,y_n>0$, $y\ge\max_iy_i$, $t\ge2$, $0<\alpha<1$, $\beta=1-\alpha$, and $B^2(-\infty,Y)<\infty$. If condition (1.4),
--   $$\max\Big[t,\ \log\Big(\frac{\beta xy^{t-1}}{A(t;0,Y)}+1\Big)\Big]\ge\frac{\alpha xy}{e^tB^2(-\infty,Y)},$$
--   holds, then for the truncated sum $\tilde S_n$
--   $$P(\tilde S_n\ge x)\le P_6=\exp\Big\{-\frac{\alpha x(\alpha x/2-\mu(-\infty,Y))}{e^tB^2(-\infty,Y)}\Big\}.$$
--
--   The page proves it under $h_1\le\max[t/y,h_2]$, which is equivalent to (1.4); with (1.8) it gives (1.5).
--
--   **Formalization Note** Condition (1.4) is `cond_1_4`, which includes the page's limiting case $A(t;0,Y)=0$ (logarithm $+\infty$). If $B^2(-\infty,Y)=0$, `P6` takes the page's limiting value $0$ (then $\tilde X_i=0$ a.s. and $P(\tilde S_n\ge x)=0$). Finiteness of $B^2(-\infty,Y)$ is assumed summand by summand.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 751, proof of Theorem 1.3, (1.19)

import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem eq_1_19 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (y : ℝ) (hy0 : 0 < y) (hyy : ∀ i, yv i ≤ y)
    (t : ℝ) (ht : 2 ≤ t)
    (α β : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hβ : β = 1 - α)
    (hL2 : ∀ i, IntegrableOn (fun ω => X i ω ^ 2) {ω | X i ω ≤ yv i} P)
    (h14 : cond_1_4 t α β x y (B2Y P X yv) (AY P X yv t)) :
    P.real {ω | x ≤ St X yv ω} ≤ P6 t α x (muY P X yv) (B2Y P X yv) := by sorry

end NagaevLD.FukNagaev
