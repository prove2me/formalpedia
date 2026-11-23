-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_tail_regularity_left_continuous
-- name    : Kyprianou.Ch08.StageB.actual_height_tail_regularity_left_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T22:04:01.284093+00:00
-- url     : https://prove2.me/theorems/8dca645c-459c-443d-b349-8419d539f680
-- title:
--   Theorem 8.2 actual-height tail regularity with closed-tail left continuity
-- statement:
--   Authorised source-faithful correction of Kyprianou.Ch08.StageB.actual_height_tail_regularity (cb2a2350-eb86-4275-a402-31ab4d6297f3). The original parameters, no-drawdown event, discounted payoff, preamble, pinned revision, antitone conjunct, unit-limit conjunct and left-limit conjunct are preserved verbatim. The second conjunct is changed from right continuity on Set.Ici h₀ to left continuity on Set.Iic h₀. This is mathematically necessary: the closed-tail law has S(h) = exp (-(n (Ici h)).toReal). If the excursion-height measure n has an atom at h₀, then Ici h loses exactly that atom immediately to the right of h₀, so S has a fixed-size downward jump there and F(h) = -Real.log (S h) has a corresponding fixed-size upward jump. Hence right continuity at such h₀ is false for permitted atomic excursion laws. A fixed-size downward-jump example is obtained by taking n with a single atom of mass c > 0 at h₀ and no mass in (h₀, h₀+ε): S(h₀)=exp(-c) while S(h)=1 for h₀<h<h₀+ε, so F(h₀)=c but F(h)=0 to the right. The closed tail is left continuous because Ici h gains no mass as h increases to h₀ from below. The final left-limit conjunct is distinct and remains valid.
-- source:
--   Source-faithful correction of authoritative target cb2a2350-eb86-4275-a402-31ab4d6297f3 at pinned Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474. Only the second conjunct's side Set.Ici h₀ is changed to Set.Iic h₀; the theorem name is changed to identify the replacement. Declared defect: closed-tail atomic downward jumps invalidate right continuity.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.actual_height_tail_regularity_left_continuous
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    AntitoneOn (fun h => -Real.log (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) (Set.Ioi 0) ∧
    (∀ h₀ : ℝ, 0 < h₀ → ContinuousWithinAt (fun h => -Real.log (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) (Set.Iic h₀) h₀) ∧
    Tendsto (fun h => -Real.log (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) atTop (nhds 0) ∧
    (∀ y : ℝ, 0 < y → Tendsto (fun s => -(-Real.log (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 s ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))) (nhdsWithin y (Set.Iio y)) (nhds (-(-Real.log (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 y ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))))) := by
  sorry
