-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_restart_payoff_split
-- name    : Kyprianou.Ch08.StageB.source_result81_restart_payoff_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T13:13:46.021787+00:00
-- url     : https://prove2.me/theorems/b0b69794-330e-4301-89b9-d19ecb9fa31f
-- title:
--   Pathwise split at the upper exit
-- statement:
--   Càdlàg right limits exclude a finite tie between crossings of levels 0 and a. On upper-first paths the upward crossing reaches a exactly, since positive jumps are excluded. Translate the lower crossing set by the upper time and use multiplicativity of discount. On lower-first paths the original payoff is the lower payoff, and an infinite tie gives zero.
-- source:
--   Kyprianou (2006), Chapter 8, proof of (8.9), p. 215. Decomposition of 3c242566-b9e1-49b0-bbd8-ab10f9c26428.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory Filter Set Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_restart_payoff_split
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    (hneg : ∀ᵐ ω ∂P, ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Tendsto (fun s => D.X s ω) (nhdsWithin t (Iio t)) (nhds l) → D.X t ω ≤ l)
    (q x a : ℝ) (hq : 0 ≤ q) (ha : 0 < a) (hxa : x ≤ a) :
    let L := tauMinus (shifted D.X x) 0
    let U := tauPlus (shifted D.X x) a
    let low := fun ω => if L ω < U ω then discountedAt q (L ω) else 0
    let restart := fun ω =>
      if U ω < L ω then
        WithTop.recTopCoe 0 (fun t =>
          discountedAt q (t : WithTop ℝ≥0) *
            discountedAt q (tauMinus
              (fun s (_ : Unit) => a + (D.X (t + s) ω - D.X t ω)) 0 ())) (U ω)
      else 0
    ∀ᵐ ω ∂P, discountedAt q (L ω) = low ω + restart ω := by
  sorry
