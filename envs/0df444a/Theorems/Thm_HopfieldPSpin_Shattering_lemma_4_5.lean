-- Prove2me | Theorems.Thm_HopfieldPSpin_Shattering_lemma_4_5
-- name    : HopfieldPSpin.Shattering.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:07:47.589525+00:00
-- url     : https://prove2.me/theorems/229d7249-a2f2-4c5a-863c-208d1e0ca9f6
-- title:
--   Lemma 4.5 — tail bound $\mathbb P(|Y|\ge u)\le\exp\{-\frac p{2e}(u/K)^{2/p}\}$ from (4.9)
-- statement:
--   Let $Y$ be a random variable on a probability space satisfying (4.9), $\|Y\|_{L^q}\le(q-1)^{p/2}\|Y\|_{L^2}$ for every real $q\ge2$, and let $K>0$ with $\|Y\|_2\le K$. For every $u\ge K(2e)^{p/2}$,
--   $$\mathbb P(|Y|\ge u)\le\exp\Big\{-\frac p{2e}\Big(\frac uK\Big)^{2/p}\Big\}.$$
--   It controls the large values of the one-pattern fields in Proposition 4.8.
--
--   Differences from the source:
--   - encoding: a random variable $Y$ for which (4.9) holds, $\|Y\|_2\le K$ → a measurable `Y : Ω → ℝ` on a probability space, (4.9) as a hypothesis for every real $q\ge2$ with `eLpNorm`, `eLpNorm Y 2 P ≤ ofReal K`; the standing degree $p\ge3$ as a binder; reason: a random variable is measurable; the norms are the same
-- source:
--   Kızıldağ, Şahin, Hopfield Model with p-spin Interactions: Shattering, Disorder Chaos and Sampling Hardness, STOC 2027 submission (manuscript sha256 4bbdc838…), p. 18 (PDF 20), Lemma 4.5

import Mathlib

open MeasureTheory

namespace HopfieldPSpin.Shattering

/-- Lemma 4.5 (p. 18): if a random variable `Y` satisfies (4.9) for every real `q ≥ 2` and
`‖Y‖₂ ≤ K` with `K > 0`, then for `u ≥ K (2e)^{p/2}`,
`P(|Y| ≥ u) ≤ exp(−(p/(2e)) (u/K)^{2/p})`. -/
theorem lemma_4_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℕ) (hp : 3 ≤ p) (Y : Ω → ℝ) (hY : Measurable Y)
    (h49 : ∀ q : ℝ, 2 ≤ q →
      eLpNorm Y (ENNReal.ofReal q) P ≤ ENNReal.ofReal ((q - 1) ^ ((p : ℝ) / 2)) * eLpNorm Y 2 P)
    (K : ℝ) (hK : 0 < K) (hYK : eLpNorm Y 2 P ≤ ENNReal.ofReal K)
    (u : ℝ) (hu : K * (2 * Real.exp 1) ^ ((p : ℝ) / 2) ≤ u) :
    P {ω | u ≤ |Y ω|} ≤
      ENNReal.ofReal (Real.exp (-((p : ℝ) / (2 * Real.exp 1) * (u / K) ^ (2 / (p : ℝ))))) := by sorry

end HopfieldPSpin.Shattering
