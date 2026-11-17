-- Prove2me | Theorems.Thm_Kyprianou_Ch07_kestenTruncatedTailIntegralMajorant
-- name    : Kyprianou.Ch07.kestenTruncatedTailIntegralMajorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T23:53:45.700869+00:00
-- url     : https://prove2.me/theorems/35ac4e18-0217-4398-8405-752cd657f60c
-- title:
--   Kesten: truncated convolution-tail integral preserves a pointwise tail majorant
-- statement:
--   If μ((y,infinity))≤C G((y,infinity)) at all y>0 and the shifted upper-tail function of G is measurable, then over the truncated domain a≤x−T with T>0 the lower integral of μ((x−a,infinity)) against G is at most C times the corresponding integral of G((x−a,infinity)). This is the measure-theoretic operator inequality needed to bound the Kesten induction by its supremum tail ratio.
-- source:
--   Kyprianou (2006), Chapter 7, proof of Lemma 7.14, printed pp.201–202, original PDF pp.210–211; exact pinned private remote source compiler evidence.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.kestenTruncatedTailIntegralMajorant
    (G mu : Measure Real) (x T : Real) (hT : 0 < T)
    (C : ENNReal)
    (hMaj : ∀ y : Real, 0 < y →
      mu (Set.Ioi y) ≤ C * G (Set.Ioi y))
    (hMeas : Measurable (fun a : Real => G (Set.Ioi (x - a)))) :
    (∫⁻ a : Real in Set.Iic (x - T),
      mu (Set.Ioi (x - a)) ∂G) ≤
      C * (∫⁻ a : Real in Set.Iic (x - T),
        G (Set.Ioi (x - a)) ∂G) := by
  sorry
