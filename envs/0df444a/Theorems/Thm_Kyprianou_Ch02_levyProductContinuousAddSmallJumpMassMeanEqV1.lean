-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyProductContinuousAddSmallJumpMassMeanEqV1
-- name    : Kyprianou.Ch02.levyProductContinuousAddSmallJumpMassMeanEqV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:00:55.535805+00:00
-- url     : https://prove2.me/theorems/8168ef5f-7877-494c-b466-f8d5d22eaf0d
-- title:
--   Independent product addition of a continuous process preserves expected actual jump mass
-- statement:
--   On the product probability space, all continuous-component paths leave the original cadlag jumps unchanged on one a.e. event lifted from P. Equality of expected jump mass follows by measurability of the original jump functional and the probability product marginal identity. No distributional assumption on the added continuous process is required.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12; LeanLevy path construction and generic Avram finite-cylinder path law.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyProductContinuousAddSmallJumpMassMeanEqV1
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Λ → ℝ)
    (hX : IsLevyProcess X P) (hY : ∀ η : Λ, Continuous (fun t => Y t η))
    (T : ℝ≥0) :
    (∫⁻ p : Ω × Λ, ∑' s : Set.Ioc (0 : ℝ≥0) T,
        ENNReal.ofReal
          (if |(fun t (q : Ω × Λ) => X t q.1 + Y t q.2) (s : ℝ≥0) p -
                Function.leftLim (fun u : ℝ≥0 => (fun t (q : Ω × Λ) => X t q.1 + Y t q.2) u p) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |(fun t (q : Ω × Λ) => X t q.1 + Y t q.2) (s : ℝ≥0) p -
                Function.leftLim (fun u : ℝ≥0 => (fun t (q : Ω × Λ) => X t q.1 + Y t q.2) u p) (s : ℝ≥0)|
           else 0) ∂(P.prod Q)) =
      (∫⁻ ω : Ω, ∑' s : Set.Ioc (0 : ℝ≥0) T,
        ENNReal.ofReal
          (if |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|
           else 0) ∂P) := by
  sorry
