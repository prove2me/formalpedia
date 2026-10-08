-- Prove2me | Theorems.Thm_NagaevLD_FukNagaev_lemma_1_4_a
-- name    : NagaevLD.FukNagaev.lemma_1_4_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:27.425263+00:00
-- url     : https://prove2.me/theorems/e8070f43-cb03-4377-8899-c6e41ecf9a52
-- title:
--   Lemma 1.4 (1.10), p. 749 — log Ee^{hX} ≤ hμ + e^tβh²/2 for X ≤ b a.s. and 0 < h ≤ t/b
-- statement:
--   Let $X$ be a random variable with $P(X>b)=0$ for some $b>0$, finite second moment, $\mu=\mathbb EX$ and $\beta=\mathbb EX^2$, and let $t\ge2$. Then for $0<h\le t/b$,
--   $$\log\mathbb Ee^{hX}\le h\mu+\frac{e^t\beta h^2}{2}.$$
--
--   This is the first half of Lemma 1.4, the cumulant bound applied to each truncated summand in the proof of the Fuk–Nagaev inequality.
--
--   **Formalization Note** Here $\beta$ is the second moment $\mathbb EX^2$ of the lemma, not the $\beta=1-\alpha$ of Theorem 1.3. The page writes $\beta=\mathbb EX^2$ as a number, so $X\in L^2$ is assumed (without it Lean's integral would return $0$). The exponent $t$ is that of the section, "the case $t\ge2$" (p. 748); the lemma uses only $t\ge0$.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 749, Lemma 1.4, (1.10)

import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem lemma_1_4_a {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (b : ℝ) (hb : 0 < b) (hXb : P {ω | b < X ω} = 0)
    (t : ℝ) (ht : 2 ≤ t)
    (hL2 : MemLp X 2 P) (h : ℝ) (hh : 0 < h) (hht : h ≤ t / b) :
    Real.log (∫ ω, Real.exp (h * X ω) ∂P) ≤
      h * (∫ ω, X ω ∂P) + Real.exp t * (∫ ω, X ω ^ 2 ∂P) * h ^ 2 / 2 := by sorry

end NagaevLD.FukNagaev
