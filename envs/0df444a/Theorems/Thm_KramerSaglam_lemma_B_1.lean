-- Prove2me | Theorems.Thm_KramerSaglam_lemma_B_1
-- name    : KramerSaglam.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:04:05.663198+00:00
-- url     : https://prove2.me/theorems/19971863-27e5-48ec-8858-79346f765fef
-- title:
--   Lemma B.1 — quadratic bounds on the binary divergence
-- statement:
--   For $a\in[0,1]$ and $b\in[1/2,1)$,
--   $$
--   \frac{2(a-b)^2}{\ln 2}\;\le\;D_2(a\,\|\,b)\;\le\;\frac{\ln(1/b)}{(1-b)^2\ln 2}\,(a-b)^2 .
--   $$
--   The lower bound holds for every $b\in(0,1)$, and complementing $a,b$ gives the upper bound for $b<1/2$:
--   $$
--   D_2(a\,\|\,b)\le\frac{\ln(1/(1-b))}{b^2\ln 2}\,(a-b)^2\qquad(0<b<1/2).
--   $$
--
--   Here $D_2$ is the binary Kullback–Leibler divergence in bits. The lower bound is Pinsker's inequality for bits; the upper bound, averaged over a conditional mean, gives Lemma 2.2.
--
--   Differences from the source:
--   - encoding: "complementing a, b gives the corresponding upper bound for b < 1/2" → the complemented bound written out, D₂(a ∥ b) ≤ ln(1/(1−b))/(b² ln 2)·(a − b)² for 0 < b < 1/2; reason: D₂(a ∥ b) = D₂(1 − a ∥ 1 − b), so this is the sentence's bound
-- source:
--   Kramer, Saglam, On the most informative Boolean function under noise, arXiv:2611.05430 (held copy sha256 d787ef8d…), Lemma B.1, p.14

import Mathlib
import Definitions.Def_KramerSaglam_Scalars

namespace KramerSaglam

/-- **Lemma B.1.** D. Kramer, M. Saglam, *On the most informative Boolean function under noise*, arXiv:2611.05430 (held copy sha256 d787ef8d…), p.14. The two-sided bound for `b ∈ [1/2, 1)`, the lower bound for every
`b ∈ (0, 1)`, and the complemented upper bound for `b < 1/2`. -/
theorem lemma_B_1 (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    (∀ b ∈ Set.Ico (1 / 2 : ℝ) 1,
      2 * (a - b) ^ 2 / Real.log 2 ≤ D2 a b ∧
        D2 a b ≤ Real.log (1 / b) / ((1 - b) ^ 2 * Real.log 2) * (a - b) ^ 2) ∧
    (∀ b ∈ Set.Ioo (0 : ℝ) 1, 2 * (a - b) ^ 2 / Real.log 2 ≤ D2 a b) ∧
    (∀ b ∈ Set.Ioo (0 : ℝ) (1 / 2),
      D2 a b ≤ Real.log (1 / (1 - b)) / (b ^ 2 * Real.log 2) * (a - b) ^ 2) := by sorry

end KramerSaglam
