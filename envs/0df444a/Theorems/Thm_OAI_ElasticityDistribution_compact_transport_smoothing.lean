-- Prove2me | Theorems.Thm_OAI_ElasticityDistribution_compact_transport_smoothing
-- name    : OAI.ElasticityDistribution.compact_transport_smoothing
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:39:07.563916+00:00
-- url     : https://prove2.me/theorems/20ea92e4-7679-4ca6-ba8f-29f411fd9bd6
-- title:
--   OAI.ElasticityDistribution.compact_transport_smoothing: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityDistribution.compact_transport_smoothing` of [lean/OAI/MathematicalPhysics/Elasticity/Smoothing.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Smoothing.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityDistribution`, with `open Set MeasureTheory TemperedDistribution`, `open scoped SchwartzMap LineDeriv ENNReal BigOperators`, `open ElasticityRegularity`):
--
--   ```lean
--   theorem compact_transport_smoothing (L : (P × ℂ) ≃L[ℝ] X)
--       {K B B₀ : Set X} (hK : IsCompact K) (hB₀ : IsOpen B₀) (hKB : K⊆B₀)
--       (A : n → n → Coeff) (W : n → L2Space) (a : n → Test)
--       (hext : ∀ i,LocalEq Kᶜ (W i : Dist) (a i : Dist))
--       (he : ∀ i,LocalEq B (planeDerivative (L (0,1)) (L (0,Complex.I)) (W i : Dist)+
--         ∑ j,A i j • (W j : Dist)) 0)
--       (g : X → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
--       (hs : tsupport g⊆B) (h1 : EqOn g 1 B₀) :
--       ∃ v : n → Test,(∀ i,(W i : Dist)=(v i : Dist)) ∧
--         ∀ i,tsupport (v i-a i : Test)⊆K
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Smooth`, `OAI.ElasticityAugmented.X`, `OAI.ElasticityDistribution.Coeff`, `OAI.ElasticityDistribution.Dist` and `OAI.ElasticityDistribution.X` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityDistribution.L2Space`, `OAI.ElasticityDistribution.LocalEq`, `OAI.ElasticityDistribution.Test` and `OAI.ElasticityDistribution.instSMulSubtypeForallXComplexMemSubalgebraSmoothCoeffDist` (definitions bundle `OAIQ6El004` of this split); `OAI.ElasticityDistribution.planeDerivative` (definitions bundle `OAIQ6El005` of this split).
--
--   **Used by.** The proofs of `OAI_ElasticityDistribution_weak_leading_smooth` and `OAI.Elasticity.dn_smooth_transport_column` of this split import it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Smoothing.lean (declaration OAI.ElasticityDistribution.compact_transport_smoothing)

import Mathlib
import Definitions.Def_OAIQ6El004
import Definitions.Def_OAIQ6El005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityDistribution
open Set MeasureTheory TemperedDistribution

open scoped SchwartzMap LineDeriv ENNReal BigOperators
open ElasticityRegularity
variable {n P : Type*} [Fintype n]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)]

theorem compact_transport_smoothing (L : (P × ℂ) ≃L[ℝ] X)
    {K B B₀ : Set X} (hK : IsCompact K) (hB₀ : IsOpen B₀) (hKB : K⊆B₀)
    (A : n → n → Coeff) (W : n → L2Space) (a : n → Test)
    (hext : ∀ i,LocalEq Kᶜ (W i : Dist) (a i : Dist))
    (he : ∀ i,LocalEq B (planeDerivative (L (0,1)) (L (0,Complex.I)) (W i : Dist)+
      ∑ j,A i j • (W j : Dist)) 0)
    (g : X → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g⊆B) (h1 : EqOn g 1 B₀) :
    ∃ v : n → Test,(∀ i,(W i : Dist)=(v i : Dist)) ∧
      ∀ i,tsupport (v i-a i : Test)⊆K := by
  sorry
end ElasticityDistribution
open Set Filter TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators Topology

end

end OAI
end
