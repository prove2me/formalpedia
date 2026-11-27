-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45CutoffSupplyV1
-- name    : Kyprianou.Ch04.exercise45CutoffSupplyV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-27T00:23:36.010438+00:00
-- url     : https://prove2.me/theorems/1975c10f-d47e-49b0-9bdc-0e66c99cf126
-- title:
--   Supply physical cutoff states and left limits with exact initial values
-- statement:
--   With the time-zero atom removed, the explicit compensated cutoff states start exactly at the original Levy process initial value, and one can choose a left-limit version at each positive cutoff.
-- source:
--   Kyprianou Exercise 4.5

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
open Kyprianou.Ch04

namespace Kyprianou.Ch04
theorem exercise45CutoffSupplyV1 :
∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Xleft : NNReal → Ω → ℝ) (hLevy : IsLevyProcess X P)
    (triplet : LevyKhintchineTriple) [SigmaFinite triplet.levyMeasure]
    (Q : PoissonRandomMeasure.{0,0,0} P triplet.levyMeasure)
    (hQLaw : ∀ᵐ w ∂P, Q.N w = pathJumpMeasure X Xleft w)
    (hQ0 : ∀ w, Q.N w (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0),
    let B := {x : ℝ | 1 ≤ |x|}
    let A (e : ℝ) := {x : ℝ | e < |x| ∧ |x| < 1}
    let V (t : NNReal) (w : Ω) := triplet.drift * (t : ℝ) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ B, z.2 ∂(Q.N w)
    let Y (e : ℝ) (t : NNReal) (w : Ω) := V t w +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ A e, z.2 ∂(Q.N w)) -
      (t : ℝ) * ∫ x in A e, x ∂triplet.levyMeasure
    ∃ L : ℝ → NNReal → Ω → ℝ,
      (∀ e w, 0 < e → e < 1 → Y e 0 w = X 0 w) ∧
      (∀ e : ℝ, 0 < e → e < 1 → ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
        Tendsto (fun s => Y e s w) (nhdsWithin t (Iio t)) (nhds (L e t w))) := by
  sorry
end Kyprianou.Ch04
