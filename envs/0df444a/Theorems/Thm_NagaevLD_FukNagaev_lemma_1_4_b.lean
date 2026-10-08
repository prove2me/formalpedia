-- Prove2me | Theorems.Thm_NagaevLD_FukNagaev_lemma_1_4_b
-- name    : NagaevLD.FukNagaev.lemma_1_4_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:44.187048+00:00
-- url     : https://prove2.me/theorems/c2f60a45-11b7-4b43-9212-b51944a04d1c
-- title:
--   Lemma 1.4 (1.11), p. 749 — log Ee^{hX} ≤ hμ + e^tβh²/2 + α_t(e^{hb} − 1 − hb)/b^t for h > t/b
-- statement:
--   Let $X$ be a random variable with $P(X>b)=0$ for some $b>0$, finite second moment, $\mu=\mathbb EX$, $\beta=\mathbb EX^2$, and $\alpha_t=\int_{u\ge0}u^t\,dF(u)=\mathbb E[X^t;X\ge0]$, where $F(u)=P(X<u)$ and $t\ge2$. Then for $h>t/b$,
--   $$\log\mathbb Ee^{hX}\le h\mu+\frac{e^t\beta h^2}{2}+\frac{\alpha_t\,(e^{hb}-1-hb)}{b^t}.$$
--
--   This is the second half of Lemma 1.4; the extra term controls the contribution of large positive values of $X$, which is where the polynomial part of the Fuk–Nagaev bound comes from.
--
--   **Formalization Note** $\beta$ is $\mathbb EX^2$, not $1-\alpha$. $X\in L^2$ is assumed, as for (1.10). $u^t$ is a real power.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 749, Lemma 1.4, (1.11)

import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem lemma_1_4_b {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (b : ℝ) (hb : 0 < b) (hXb : P {ω | b < X ω} = 0)
    (t : ℝ) (ht : 2 ≤ t)
    (hL2 : MemLp X 2 P) (h : ℝ) (hht : t / b < h) :
    Real.log (∫ ω, Real.exp (h * X ω) ∂P) ≤
      h * (∫ ω, X ω ∂P) + Real.exp t * (∫ ω, X ω ^ 2 ∂P) * h ^ 2 / 2 +
        (∫ ω in {ω | 0 ≤ X ω}, X ω ^ t ∂P) * (Real.exp (h * b) - 1 - h * b) / b ^ t := by sorry

end NagaevLD.FukNagaev
