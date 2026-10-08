-- Prove2me | Theorems.Thm_NagaevLD_FukNagaev_theorem_1_3
-- name    : NagaevLD.FukNagaev.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:53.080984+00:00
-- url     : https://prove2.me/theorems/064c49ed-97ba-47ed-bcc4-7c04d3201ee8
-- title:
--   Theorem 1.3, p. 749 — P(S_n ≥ x) ≤ ΣP(X_i > y_i) + P₆ under (1.4); < … + P₄ under (1.6); < … + P₅ if also β ≥ tα/2 or βx ≥ μ(−∞, Y)
-- statement:
--   **The Fuk–Nagaev inequality.** Let $X_1,\dots,X_n$ be independent random variables with $F_i(u)=P(X_i<u)$ and $S_n=X_1+\dots+X_n$. Let $x>0$, let $y_1,\dots,y_n$ be positive numbers and $y\ge\max_iy_i$. Write
--   $$\mu(-\infty,Y)=\sum_{i=1}^n\int_{u\le y_i}u\,dF_i(u),\quad B^2(-\infty,Y)=\sum_{i=1}^n\int_{u\le y_i}u^2\,dF_i(u),\quad A(t;0,Y)=\sum_{i=1}^n\int_{0\le u\le y_i}|u|^t\,dF_i(u),$$
--   and assume $B^2(-\infty,Y)<\infty$. Suppose $t\ge2$, $0<\alpha<1$ and $\beta=1-\alpha$.
--
--   1. If (1.4) $\ \max\big[t,\log\big(\frac{\beta xy^{t-1}}{A(t;0,Y)}+1\big)\big]\ge\frac{\alpha xy}{e^tB^2(-\infty,Y)}$, then
--   $$P(S_n\ge x)\le\sum_{i=1}^nP(X_i>y_i)+P_6.$$
--   2. If (1.6) $\ \max\big[t,\log\big(\frac{\beta xy^{t-1}}{A(t;0,Y)}+1\big)\big]<\frac{\alpha xy}{e^tB^2(-\infty,Y)}$, then
--   $$P(S_n\ge x)<\sum_{i=1}^nP(X_i>y_i)+P_4.$$
--   3. If (1.6) holds and at least one of $\beta\ge t\alpha/2$, $\beta x\ge\mu(-\infty,Y)$ holds, then
--   $$P(S_n\ge x)<\sum_{i=1}^nP(X_i>y_i)+P_5.$$
--
--   Here
--   $$P_4=\exp\Big\{\beta\frac xy-\Big(\big(1-\tfrac\alpha2\big)\frac xy-\frac{\mu(-\infty,Y)}y\Big)\log\Big(\frac{\beta xy^{t-1}}{A(t;0,Y)}+1\Big)\Big\},$$
--   $$P_5=\exp\Big\{\Big(\beta-\frac{t\alpha}2\Big)\frac xy-\Big(\beta\frac xy-\frac{\mu(-\infty,Y)}y\Big)\log\Big(\frac{\beta xy^{t-1}}{A(t;0,Y)}+1\Big)\Big\},\quad P_6=\exp\Big\{-\frac{\alpha x(\alpha x/2-\mu(-\infty,Y))}{e^tB^2(-\infty,Y)}\Big\}.$$
--
--   The inequality bounds the upper tail of a sum of independent summands by a "large single summand" term $\sum_iP(X_i>y_i)$ plus an exponential term in truncated moments, with no assumption beyond finiteness of the truncated moments. Its corollaries (1.23) and (1.24) are the familiar Fuk–Nagaev bound $P(S_n\ge x)\le c_t^{(1)}A_t^+x^{-t}+\exp\{-c_t^{(2)}x^2/B_n^2\}$ for centred summands.
--
--   **Formalization Note**
--   1. Part 3 is printed "If, *instead of* (1.6), at least one of the conditions … is fulfilled"; the proof (p. 752) establishes it "if, *in addition*" to (1.6), and under (1.4) only gives $P_6$. The statement follows the proof.
--   2. On the page $A(t;0,Y)=0$ makes the logarithm $+\infty$, so (1.4) holds. Lean's division by zero would give the logarithm $0$; condition (1.4) is therefore `cond_1_4`, which contains the disjunct $A(t;0,Y)=0$, and (1.6) is `cond_1_6`, which contains $A(t;0,Y)>0$. If $B^2(-\infty,Y)=0$, `P6` takes the page's limiting value $0$ ($\exp\{-\infty\}$), not Lean's $\exp(\cdot/0)=1$.
--   3. $B^2(-\infty,Y)<\infty$ is assumed as integrability of $X_i^2$ on $\{X_i\le y_i\}$ for each $i$: on the page an infinite $B^2(-\infty,Y)$ makes the bound trivial, while Lean would replace it by $0$ and the statement would become false.
--   4. $y>0$ is stated explicitly (it follows from $y\ge y_i>0$ when $n\ge1$). Indices run over `Fin n`. Integrals against $dF_i$ are expectations over the corresponding events.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 749, Theorem 1.3, (1.4)–(1.7a); P₄, P₅, P₆ defined on p. 748

import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem theorem_1_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (y : ℝ) (hy0 : 0 < y) (hyy : ∀ i, yv i ≤ y)
    (t : ℝ) (ht : 2 ≤ t)
    (α β : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hβ : β = 1 - α)
    (hL2 : ∀ i, IntegrableOn (fun ω => X i ω ^ 2) {ω | X i ω ≤ yv i} P) :
    (cond_1_4 t α β x y (B2Y P X yv) (AY P X yv t) →
        P.real {ω | x ≤ S n X ω} ≤
          ∑ i, P.real {ω | yv i < X i ω} + P6 t α x (muY P X yv) (B2Y P X yv)) ∧
      (cond_1_6 t α β x y (B2Y P X yv) (AY P X yv t) →
        P.real {ω | x ≤ S n X ω} <
          ∑ i, P.real {ω | yv i < X i ω} + P4 t α β x y (muY P X yv) (AY P X yv t)) ∧
      (cond_1_6 t α β x y (B2Y P X yv) (AY P X yv t) →
        (β ≥ t * α / 2 ∨ β * x ≥ muY P X yv) →
        P.real {ω | x ≤ S n X ω} <
          ∑ i, P.real {ω | yv i < X i ω} + P5 t α β x y (muY P X yv) (AY P X yv t)) := by sorry

end NagaevLD.FukNagaev
