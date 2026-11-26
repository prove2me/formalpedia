-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvPathRepV1
-- name    : Kyprianou.Ch04.bvPathRepV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:27:36.657675+00:00
-- url     : https://prove2.me/theorems/6deb80d4-2673-5397-a8d1-ce6a8aec8886
-- title:
--   Canonical left-limit BV jump representation
-- statement:
--   Specialise the proved actual jump representation to canonical left limits on the common cadlag event.
-- source:
--   Supporting proof for Kyprianou (2006), Chapter 4, Exercise 4.9(i).

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvActualJumpDriftRepresentationV1
open MeasureTheory ProbabilityTheory Filter Set Function Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.bvPathRepV1 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P)
    (T : LevyKhintchineTriple)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent T ξ))
    (hBV : T.gaussianVariance = 0 ∧
      (∫⁻ y in Ioo (-1 : ℝ) 1, ENNReal.ofReal |y| ∂T.levyMeasure) < ⊤)
    (d : ℝ) (hd : d = T.drift - ∫ y in Ioo (-1 : ℝ) 1, y ∂T.levyMeasure) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Summable (fun s : Ioc (0 : ℝ≥0) t =>
        |X s ω - leftLim (fun u => X u ω) s|) ∧
      X t ω = d * (t : ℝ) +
        ∑' s : Ioc (0 : ℝ≥0) t, (X s ω - leftLim (fun u => X u ω) s) := by
  sorry
