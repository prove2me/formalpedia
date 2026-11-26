-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45PhysicalGridUCPV5
-- name    : Kyprianou.Ch04.exercise45PhysicalGridUCPV5
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T21:42:24.363136+00:00
-- url     : https://prove2.me/theorems/403915af-db38-48f4-8518-f18b521338cd
-- title:
--   Bounded physical weighted grids converge in outer probability from uniform path convergence
-- statement:
--   Bounded physical weighted grids converge in outer probability from uniform path convergence
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii)

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45PhysicalGridUCPV5 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y H J : NNReal → Ω → ℝ)
    (hmY : ∀ t, AEMeasurable (Y t) P)
    (hmH : ∀ t, AEMeasurable (fun w => if t = 0 then 0 else H t w) P)
    (hrY : ∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => Y s w) (Ici t) t)
    (T : NNReal) (K : ℝ) (hK : 0 ≤ K) (hb : ∀ w, |H 0 w| ≤ K) :
    let G : (NNReal → Ω → ℝ) → ℕ → NNReal → Ω → ℝ := fun W n t w =>
      ∑ k ∈ Finset.range n, W (T * (k : NNReal) / (n : NNReal)) w *
        (Y (min t (T * ((k+1 : ℕ) : NNReal) / (n : NNReal))) w -
         Y (min t (T * (k : NNReal) / (n : NNReal))) w)
    (∀ᵐ w ∂P, ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T, |G H n t w - J t w| < δ) →
    ∀ δ : ℝ, 0 < δ → Tendsto
      (fun n => (P {w | ∃ t ≤ T, δ ≤ |G H n t w - J t w|}).toReal) atTop (nhds 0) := by
  sorry
