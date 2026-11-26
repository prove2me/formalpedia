-- Prove2me | Theorems.Thm_Kyprianou_Ch04_actualLargeJumpGridCompactV1
-- name    : Kyprianou.Ch04.actualLargeJumpGridCompactV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:53:47.75294+00:00
-- url     : https://prove2.me/theorems/c27ca3da-1bc5-5d8c-a1ff-3f3b3d254cb6
-- title:
--   Original large-jump grid integral for locally bounded continuous weights
-- statement:
--   Finite retained atoms and compact-horizon boundedness give the physical large-jump integral for the original Levy path, without a global bound on the weight.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii)-(iv).

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson Set Filter Topology
open scoped NNReal ENNReal Classical
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem actualLargeJumpGridCompactV1 :
∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (N : PoissonRandomMeasure.{0,0,0} P ν) (X L X2 : NNReal → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hL : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun u => X u w) (𝓝[<] t) (𝓝 (L t w)))
    (hN : ∀ᵐ w ∂P, N.N w = Kyprianou.Ch04.pathJumpMeasure X L w)
    (b : ℝ) (h2 : ∀ t w, X2 t w = b * (t : ℝ) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂(N.N w))
    (g : ℝ → ℝ → ℝ)
    (hg : ContinuousOn (fun z : ℝ × ℝ => g z.1 z.2) (Ici (0 : ℝ) ×ˢ univ)),
    ∀ᵐ w ∂P, ∀ T : NNReal,
      Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
        let u := T * (i : NNReal) / (n : NNReal)
        let v := T * ((i+1 : ℕ) : NNReal) / (n : NNReal)
        g (u : ℝ) (L u w) * (X2 v w - X2 u w)) atTop
        (𝓝 (b * (∫ s in Icc (0 : ℝ) (T : ℝ), g s (L s.toNNReal w)) +
          ∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
            z.2 * g z.1 (L z.1.toNNReal w) ∂(N.N w))) := by
  sorry
end Kyprianou.Ch04
