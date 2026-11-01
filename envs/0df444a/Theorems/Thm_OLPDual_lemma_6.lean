-- Prove2me | Theorems.Thm_OLPDual_lemma_6
-- name    : OLPDual.lemma_6
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T09:20:36.220121+00:00
-- url     : https://prove2.me/theorems/9fcece28-5103-425c-8ef4-0de9ad938716
-- title:
--   Lemma 6, p.42 (corrected: $1+1/\log 2$)
-- statement:
--   For all $m\ge 2$,
--
--   $$
--   \int_0^\infty\bigl(\exp(\log m-x\log m)\bigr)\wedge 1\,dx\le 1+\frac{1}{\log 2},
--   $$
--
--   where $y\wedge z=\min\{y,z\}$. This bound is used to integrate the tail coming from Proposition 3 in the proof of Theorem 1.
--
--   **Formalization Note** The integrand is asserted to be integrable on $(0,\infty)$, so the integral is a true value.
--
--   Differences from the source:
--   - correction: the integral is at most 2 → the integral is at most 1 + 1/log 2; reason: the integral equals 1 + 1/log m, which is ≈ 2.443 > 2 at m = 2; the paper’s own proof ends at 1 + 1/log 2 on p.43
--   - generalization: m the integer dimension → m real with m ≥ 2; reason: every integer m ≥ 2 is a real m ≥ 2
--   - encoding: ∫_0^∞ → Bochner integral on Ioi 0 with an IntegrableOn conjunct; reason: rules out the junk value 0
-- source:
--   Li–Ye, Online Linear Programming: Dual Convergence, New Algorithms, and Regret Bounds, arXiv:1909.05499v5 (19 Apr 2021), Lemma 6, p.42; proof p.43

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OLPDual

/-- **Lemma 6, corrected**, Li–Ye, arXiv:1909.05499v5, p.42 (PDF 42):
`∫_0^∞ (exp(log m − x log m)) ∧ 1 dx ≤ 1 + 1/log 2` for all `m ≥ 2`.
**Formalization Note** The printed constant `2` is false at `m = 2`: the integral equals
`1 + 1/log m`. The paper's own proof ends at `1 + 1/log 2` (p.43). Integrability is asserted, so the
Bochner integral is not a junk value; `m` is real. -/
theorem lemma_6 (m : ℝ) (hm : 2 ≤ m) :
    IntegrableOn (fun x : ℝ => min (Real.exp (Real.log m - x * Real.log m)) 1) (Set.Ioi 0) ∧
    ∫ x in Set.Ioi (0 : ℝ), min (Real.exp (Real.log m - x * Real.log m)) 1 ≤
      1 + 1 / Real.log 2 := by sorry

end OLPDual
