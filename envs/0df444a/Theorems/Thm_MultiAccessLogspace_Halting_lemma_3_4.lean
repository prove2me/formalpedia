-- Prove2me | Theorems.Thm_MultiAccessLogspace_Halting_lemma_3_4
-- name    : MultiAccessLogspace.Halting.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:19.172585+00:00
-- url     : https://prove2.me/theorems/d65e5d5d-ae86-4584-81f2-ca70851efbf9
-- title:
--   Lemma 3.4 — generating hyporulers
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, let $d\ge0$, $b\ge1$, and $N\ge0$, and let $H_1,\ldots,H_N$ be measurable independent identically distributed variables taking values in $\mathbb N\cup\{\infty\}$. Assume $P(H_i=h)=2^{-h}$ for every $i$ and $1\le h\le d$. No restriction is imposed on the distribution of the remaining mass outside this range. Then
--   $$
--   P\bigl((H_1,\ldots,H_N)\text{ is not a }(d,b)\text{-hyporuler}\bigr)
--   \le N\bigl(2^{-d}+2^{-(b-1)}\bigr).
--   $$
--   An infinite entry makes the list fail the hyporuler predicate. This is the generation bound for the finite random-tape timer. The bound also includes $N=0$, $d=0$, and $b=1$.
--
--   Differences from the source:
--   - encoding: independent identically distributed random variables with specified masses on [d] → measurable ENat-valued variables on an explicit probability space, independent and identically distributed; probabilities and inverse powers use ENNReal; reason: ENat retains the infinity value used on PDF p. 9; all values outside [d] cause failure, so other outside values can be identified with infinity without changing the assertion
-- source:
--   William M. Hoza, STOC 2027 submission #92 (October 2026), Lemma 3.4, PDF p. 7 (printed p. 6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/92.pdf; PDF SHA-256 92de35889559d87b5a77d83317b9c7b2c8924912fbd5c712f2af3c005c8998d8

import Mathlib
import Definitions.Def_MultiAccessLogspace_Halting_Rulers

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultiAccessLogspace.Halting

/-- Lemma 3.4 (Generating hyporulers). The `H i` are i.i.d. with values in `ℕ ∪ {∞}` and
`Pr[H i = h] = 2^{-h}` for `h ∈ [d]`; only these masses are assumed. -/
theorem lemma_3_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d b N : ℕ) (hb : 1 ≤ b) (H : Fin N → Ω → ℕ∞)
    (hmeas : ∀ i, Measurable (H i))
    (hindep : iIndepFun H P)
    (hident : ∀ i j, IdentDistrib (H i) (H j) P P)
    (hmass : ∀ i, ∀ h : ℕ, 1 ≤ h → h ≤ d → P {ω | H i ω = (h : ℕ∞)} = (2 : ℝ≥0∞)⁻¹ ^ h) :
    P {ω | ¬ IsHyporulerENat b d (List.ofFn fun i => H i ω)} ≤
      (N : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ d + (2 : ℝ≥0∞)⁻¹ ^ (b - 1)) := by sorry

end MultiAccessLogspace.Halting
