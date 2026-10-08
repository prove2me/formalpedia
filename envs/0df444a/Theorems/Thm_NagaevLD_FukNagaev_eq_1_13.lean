-- Prove2me | Theorems.Thm_NagaevLD_FukNagaev_eq_1_13
-- name    : NagaevLD.FukNagaev.eq_1_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:25.205297+00:00
-- url     : https://prove2.me/theorems/ca32c889-70d5-486f-9aa8-ef7b1bd2744d
-- title:
--   (1.13), p. 750 — ∫_{u≤b}(e^{hu} − 1 − hu)dF ≤ ∫_{u≤t/h}(e^{hu} − 1 − hu)dF ≤ e^tβh²/2 for h ≤ t/b
-- statement:
--   In the setting of Lemma 1.4 ($P(X>b)=0$, $b>0$, $\beta=\mathbb EX^2<\infty$, $t\ge2$, $F(u)=P(X<u)$), suppose $0<h\le t/b$. Then
--   $$\int_{u\le b}(e^{hu}-1-hu)\,dF(u)\le\int_{u\le t/h}(e^{hu}-1-hu)\,dF(u)\le\frac{e^t\beta h^2}{2}.$$
--
--   Together with the identity $\mathbb Ee^{hX}=1+h\mu+\int_{u\le b}(e^{hu}-1-hu)\,dF(u)$ and $\log z\le z-1$ this gives (1.10); its second inequality, which holds for every $h>0$, is also used for (1.11).
--
--   **Formalization Note** The integrals over $\{u\le c\}$ are expectations over the events $\{X\le c\}$. $X\in L^2$ is assumed, as in Lemma 1.4.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 750, proof of Lemma 1.4, (1.13)

import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem eq_1_13 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (b : ℝ) (hb : 0 < b) (hXb : P {ω | b < X ω} = 0)
    (t : ℝ) (ht : 2 ≤ t)
    (hL2 : MemLp X 2 P) (h : ℝ) (hh : 0 < h) (hht : h ≤ t / b) :
    ∫ ω in {ω | X ω ≤ b}, (Real.exp (h * X ω) - 1 - h * X ω) ∂P ≤
        ∫ ω in {ω | X ω ≤ t / h}, (Real.exp (h * X ω) - 1 - h * X ω) ∂P ∧
      ∫ ω in {ω | X ω ≤ t / h}, (Real.exp (h * X ω) - 1 - h * X ω) ∂P ≤
        Real.exp t * (∫ ω, X ω ^ 2 ∂P) * h ^ 2 / 2 := by sorry

end NagaevLD.FukNagaev
