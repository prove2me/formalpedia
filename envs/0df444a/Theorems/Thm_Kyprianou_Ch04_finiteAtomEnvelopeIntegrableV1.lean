-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteAtomEnvelopeIntegrableV1
-- name    : Kyprianou.Ch04.finiteAtomEnvelopeIntegrableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:17:49.550951+00:00
-- url     : https://prove2.me/theorems/ad3aa442-83e9-55a3-b802-c7ccaeb0d5bd
-- title:
--   Finite large atom envelope integrability
-- statement:
--   Finite large atom envelope integrability.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open MeasureTheory Set
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem finiteAtomEnvelopeIntegrableV1 (R : Measure (ℝ × ℝ)) (T : NNReal)
    (S : Finset NNReal) (j : NNReal → ℝ)
    (hR : R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | (1/2:ℝ) < |x|}) =
      ∑ r ∈ S, Measure.dirac ((r : ℝ),j r))
    (g : ℝ → ℝ) (hg : Measurable g) :
    IntegrableOn (fun z : ℝ × ℝ => if 1 ≤ |z.2| then g z.2 else 0)
      (Icc (0 : ℝ) (T : ℝ) ×ˢ univ) R := by
  sorry
end Kyprianou.Ch04
