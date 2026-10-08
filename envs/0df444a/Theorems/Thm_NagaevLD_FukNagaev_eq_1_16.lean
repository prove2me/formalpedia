-- Prove2me | Theorems.Thm_NagaevLD_FukNagaev_eq_1_16
-- name    : NagaevLD.FukNagaev.eq_1_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:28.652387+00:00
-- url     : https://prove2.me/theorems/c1546a2d-18ba-4574-b4d3-dd1a827ea504
-- title:
--   (1.16), p. 750 — ∫_{u>t/h}(e^{hu} − 1 − hu)dF(u) ≤ α_t(e^{hb} − 1 − hb)/b^t for h > t/b
-- statement:
--   In the setting of Lemma 1.4 ($P(X>b)=0$, $b>0$, $t\ge2$, $F(u)=P(X<u)$, $\alpha_t=\int_{u\ge0}u^t\,dF(u)$), suppose $h>t/b$. Then
--   $$\int_{u>t/h}(e^{hu}-1-hu)\,dF(u)\le\frac{\alpha_t\,(e^{hb}-1-hb)}{b^t}.$$
--
--   The page obtains it by writing the integrand as $\frac{e^{hu}-1-hu}{u^t}\,u^t$ and noting that $(e^{hu}-1-hu)/u^t$ increases for $u>t/h$. It bounds the upper piece of the split (1.15) in the proof of (1.11).
--
--   **Formalization Note** The integral is the expectation over the event $\{X>t/h\}$; since $P(X>b)=0$ this is the range $t/h<u\le b$. $u^t$ is a real power.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 750, proof of Lemma 1.4, (1.16)

import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem eq_1_16 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (b : ℝ) (hb : 0 < b) (hXb : P {ω | b < X ω} = 0)
    (t : ℝ) (ht : 2 ≤ t)
    (h : ℝ) (hht : t / b < h) :
    ∫ ω in {ω | t / h < X ω}, (Real.exp (h * X ω) - 1 - h * X ω) ∂P ≤
      (∫ ω in {ω | 0 ≤ X ω}, X ω ^ t ∂P) * (Real.exp (h * b) - 1 - h * b) / b ^ t := by sorry

end NagaevLD.FukNagaev
