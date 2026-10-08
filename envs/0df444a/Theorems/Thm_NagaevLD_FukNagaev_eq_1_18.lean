-- Prove2me | Theorems.Thm_NagaevLD_FukNagaev_eq_1_18
-- name    : NagaevLD.FukNagaev.eq_1_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:44.047916+00:00
-- url     : https://prove2.me/theorems/67060569-9100-4183-a499-cc4263283eb1
-- title:
--   (1.18), p. 750 — P(S̃_n ≥ x) ≤ exp{h(μ(−∞, Y) − x) + ½e^tB²(−∞, Y)h² + (e^{hy} − 1 − hy)A(t; 0, Y)/y^t} for h > t/y
-- statement:
--   In the setting of (1.17) ($X_i$ independent, $x>0$, $y_i>0$, $y\ge\max_iy_i$, $t\ge2$, $B^2(-\infty,Y)<\infty$), with $A(t;0,Y)=\sum_i\int_{0\le u\le y_i}|u|^t\,dF_i(u)$, for $h>t/y$,
--   $$P(\tilde S_n\ge x)\le\exp\Big\{h\big(\mu(-\infty,Y)-x\big)+\tfrac12e^tB^2(-\infty,Y)h^2+\frac{e^{hy}-1-hy}{y^t}A(t;0,Y)\Big\}.$$
--
--   It is (1.9) combined with Lemma 1.4 applied to every factor $\mathbb Ee^{h\tilde X_i}$; the extra term produces the polynomial bounds $P_4$, $P_5$.
--
--   **Formalization Note** As in (1.17): finiteness of $B^2(-\infty,Y)$ assumed summand by summand, $y>0$ explicit, $|u|^t$ a real power.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 750, proof of Theorem 1.3, (1.18)

import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem eq_1_18 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (y : ℝ) (hy0 : 0 < y) (hyy : ∀ i, yv i ≤ y)
    (t : ℝ) (ht : 2 ≤ t)
    (hL2 : ∀ i, IntegrableOn (fun ω => X i ω ^ 2) {ω | X i ω ≤ yv i} P)
    (h : ℝ) (hht : t / y < h) :
    P.real {ω | x ≤ St X yv ω} ≤
      Real.exp (h * (muY P X yv - x) + 1 / 2 * Real.exp t * B2Y P X yv * h ^ 2 +
        (Real.exp (h * y) - 1 - h * y) / y ^ t * AY P X yv t) := by sorry

end NagaevLD.FukNagaev
