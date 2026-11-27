-- Prove2me | Theorems.Thm_Kyprianou_Ch04_actualNormalisedSmallJumpGridPairBoundV1
-- name    : Kyprianou.Ch04.actualNormalisedSmallJumpGridPairBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:56:34.179867+00:00
-- url     : https://prove2.me/theorems/ee917a39-04a7-4b13-9278-3a8a4ff5627b
-- title:
--   actualNormalisedSmallJumpGridPairBoundV1
-- statement:
--   Uniform maximal probability bound for the actual normalised small-jump grid pair.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_actualPoissonFutureIndependenceV1
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.actualNormalisedSmallJumpGridPairBoundV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (X Xleft X2 U V L R : NNReal → Ω → ℝ)
    (F : Filtration NNReal inferInstance)
    (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (t : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Icc (0 : ℝ) (t : ℝ) ×ˢ univ → Measurable[F t] (fun w => N.N w D))
    (hN : ∀ᵐ w ∂P, N.N w = Kyprianou.Ch04.pathJumpMeasure X Xleft w)
    (c a b K : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) (hK : 0 ≤ K)
    (h2 : ∀ t w, X2 t w = c * (t : ℝ) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},z.2 ∂(N.N w))
    (hU : ∀ t w, U t w = X2 t w +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | a < |x| ∧ |x| < 1},z.2 ∂(N.N w)) -
      (t : ℝ) * (∫ x in {x : ℝ | a < |x| ∧ |x| < 1},x ∂ν))
    (hV : ∀ t w, V t w = X2 t w +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | b < |x| ∧ |x| < 1},z.2 ∂(N.N w)) -
      (t : ℝ) * (∫ x in {x : ℝ | b < |x| ∧ |x| < 1},x ∂ν))
    (hL : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => U s w) (𝓝[<] t) (𝓝 (L t w)))
    (hR : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => V s w) (𝓝[<] t) (𝓝 (R t w)))
    (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hBound : ∀ s x : ℝ, 0 ≤ s → |f s x| ≤ K)
    (hLip : ∀ s : NNReal, ∀ x y : ℝ, |f s x-f s y| ≤ K*|x-y|)
    (T : NNReal) (hT : 0 < T) (n : ℕ) (u : ℕ → NNReal) (hu : Monotone u)
    (huT : ∀ k ∈ Finset.range n, u k ≤ T) :
    let G := fun (Y Z : NNReal → Ω → ℝ) (t : NNReal) w =>
      ∑ k ∈ Finset.range n, (if u k=0 then 0 else f (u k) (Z (u k) w)) *
        ((Y (min t (u (k+1))) w-X2 (min t (u (k+1))) w)-
          (Y (min t (u k)) w-X2 (min t (u k)) w))
    ∀ δ : ℝ, 0 < δ →
      P {w | ∃ t ≤ T, δ ≤ |G U L t w-G V R t w|} ≤
        ENNReal.ofReal (4 * ((K^2 * (T : ℝ) * (1 + 4 * (T : ℝ) *
          (∫⁻ z in {z : ℝ | |z| < 1}, ENNReal.ofReal (z^2) ∂ν).toReal)) *
          (∫⁻ z in {z : ℝ | |z| ≤ b}, ENNReal.ofReal (z^2) ∂ν).toReal)) /
          ENNReal.ofReal ((δ/2)^2) := by
  sorry
