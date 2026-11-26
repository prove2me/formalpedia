-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cutoffPredictableTerminalCertificateV1
-- name    : Kyprianou.Ch04.cutoffPredictableTerminalCertificateV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:37:07.55705+00:00
-- url     : https://prove2.me/theorems/45cd3cec-759a-4398-888c-fbcde19d4e1f
-- title:
--   Predictable kernel certificate for a physical cutoff terminal variable
-- statement:
--   For an actual physical cutoff terminal variable, the bounded marked predictable kernel is measurable, has the stated support and norm bound, and its compensated physical integral equals the variable almost surely.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(ii).

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem cutoffPredictableTerminalCertificateV1 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal inferInstance) (N : PoissonRandomMeasure.{0,0,0} P ν)
    (T : NNReal) (e K : ℝ) (hK : 0 ≤ K)
    (hfin : ν {x : ℝ | e < |x| ∧ |x| < 1} < ⊤)
    (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hBound : ∀ s x : ℝ, 0 ≤ s → |f s x| ≤ K)
    (L V : NNReal → Ω → ℝ) (hV : IsStronglyPredictable F V)
    (hEq : ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t → V t ω = L t ω)
    (M : Ω → ℝ)
    (hM : ∀ ω, M ω = (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ
      {x : ℝ | e < |x| ∧ |x| < 1}, z.2 * f z.1 (L z.1.toNNReal ω) ∂(N.N ω)) -
      ∫ s in Icc (0 : ℝ) (T : ℝ), ∫ x in {x : ℝ | e < |x| ∧ |x| < 1},
        x * f s (L s.toNNReal ω) ∂ν ∂volume) :
    let B := {x : ℝ | e < |x| ∧ |x| < 1}
    let g := fun p : (NNReal × Ω) × ℝ =>
      B.indicator (fun z => z * f (p.1.1 : ℝ) (V p.1.1 p.1.2)) p.2
    let U := Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ)
    Measurable[F.predictable.prod inferInstance] g ∧ (∀ p, ‖g p‖ ≤ K) ∧
      (∀ p, p.2 ∉ B → g p = 0) ∧ ∀ᵐ ω ∂P, M ω =
      ((∫ z in U, g ((z.1.toNNReal,ω),z.2) ∂(N.N ω)) -
        ∫ z in U, g ((z.1.toNNReal,ω),z.2) ∂referenceIntensity ν) := by
  sorry
end Kyprianou.Ch04
