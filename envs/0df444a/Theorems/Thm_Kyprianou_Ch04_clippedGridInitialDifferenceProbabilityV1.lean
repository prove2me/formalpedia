-- Prove2me | Theorems.Thm_Kyprianou_Ch04_clippedGridInitialDifferenceProbabilityV1
-- name    : Kyprianou.Ch04.clippedGridInitialDifferenceProbabilityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:29:51.729773+00:00
-- url     : https://prove2.me/theorems/5a039f49-3124-58db-b3d8-49633ba3df71
-- title:
--   clippedGridInitialDifferenceProbabilityV1
-- statement:
--   The difference of two initial clipped grid cells with bounded coefficients vanishes in outer probability.
-- source:
--   Kyprianou (2006), Exercise 4.5(iii)

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Restore the arbitrary bounded initial weights of two right-continuous states. -/

theorem Kyprianou.Ch04.clippedGridInitialDifferenceProbabilityV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y H L : NNReal → Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ w, |H 0 w| ≤ K) (hL : ∀ w, |L 0 w| ≤ K)
    (hX : ∀ t, AEMeasurable (X t) P) (hY : ∀ t, AEMeasurable (Y t) P)
    (hrX : ∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => X s w) (Ici t) t)
    (hrY : ∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => Y s w) (Ici t) t)
    (T : NNReal) (hT : 0 < T) :
    let G := fun (Z W : NNReal → Ω → ℝ) (n : ℕ) (t : NNReal) w =>
      ∑ k ∈ Finset.range n, W (T * (k : NNReal) / (n : NNReal)) w *
        (Z (min t (T * ((k+1 : ℕ) : NNReal) / (n : NNReal))) w -
          Z (min t (T * (k : NNReal) / (n : NNReal))) w)
    let H0 := fun (s : NNReal) w => if s = 0 then 0 else H s w
    let L0 := fun (s : NNReal) w => if s = 0 then 0 else L s w
    ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      (P {w | ∃ t ≤ T, δ ≤ |(G X H n t w-G X H0 n t w) -
        (G Y L n t w-G Y L0 n t w)|}).toReal ≤ η := by
  sorry
