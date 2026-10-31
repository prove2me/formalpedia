-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affineMaximal_uniform_target_cap_lintegral_bound
-- name    : OAI.AffineBernstein.affineMaximal_uniform_target_cap_lintegral_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:09:48.689392+00:00
-- url     : https://prove2.me/theorems/45e85887-c95f-4201-8759-19e7d566cf9d
-- title:
--   OAI.AffineBernstein.affineMaximal_uniform_target_cap_lintegral_bound: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.affineMaximal_uniform_target_cap_lintegral_bound` of [lean/OAI/Analysis/AffineBernstein/TargetCapLIntegral.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/TargetCapLIntegral.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`):
--
--   ```lean
--   theorem affineMaximal_uniform_target_cap_lintegral_bound (n : ℕ)
--       (T : G ≃L[ℝ] (Space n × ℝ))
--       {ε r R : ℝ} (hε : 0 < ε) (hr : 0 < r) (hR : 0 ≤ R)
--       (t₀ t₁ q₀ : ℝ) :
--       ∃ C > 0, ∀ {Ω : Set (Space n)}, IsOpen Ω → Convex ℝ Ω →
--         ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω →
--         (∀ x ∈ Ω, (hessian u x).PosDef) → AffineMaximalOn Ω u →
--         ∀ (L : G ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
--           (o : Space n) (c : ℝ) (a : Space n →L[ℝ] ℝ) (b d : ℝ),
--         Metric.closedBall (L.symm ((o,c)-v)) r ⊆
--           (fun p => L.symm (p-v)) '' sourceEpigraph Ω u →
--         a o+b*c+d = q₀ →
--         ∀ {K Q : Set (Space n)}, IsCompact K → K ⊆ Ω → MeasurableSet Q → Q ⊆ K →
--         (∀ x ∈ Ω, x ∉ K → t₁+ε ≤ graphAffineFunction u a b d x) →
--         (∀ x ∈ K, graphAffineFunction u a b d x ∈ Icc t₀ (t₁+ε)) →
--         (∀ x ∈ Q, graphAffineFunction u a b d x ≤ t₁-ε) →
--         (∀ x ∈ K, ‖L.symm ((x,u x)-v)‖ ≤ R) →
--         ENNReal.ofReal (Real.rpow |(L.symm.trans T).toContinuousLinearMap.det|
--           ((n:ℝ)/((n:ℝ)+2))) *
--           (∫⁻ x in Q, ENNReal.ofReal (affineAreaDensity u x *
--             (‖targetGraphConormal u L x‖ * graphInverseMetric u a b d x))) ≤ ENNReal.ofReal C
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.affineAreaDensity`, `OAI.AffineBernstein.graphAffineFunction`, `OAI.AffineBernstein.graphInverseMetric`, `OAI.AffineBernstein.sourceEpigraph` and `OAI.AffineBernstein.targetGraphConormal` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.AffineMaximalOn`, `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.complete_affineMaximal_uniform_spherical_cap_bound` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/TargetCapLIntegral.lean (declaration OAI.AffineBernstein.affineMaximal_uniform_target_cap_lintegral_bound)

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem affineMaximal_uniform_target_cap_lintegral_bound (n : ℕ)
    (T : G ≃L[ℝ] (Space n × ℝ))
    {ε r R : ℝ} (hε : 0 < ε) (hr : 0 < r) (hR : 0 ≤ R)
    (t₀ t₁ q₀ : ℝ) :
    ∃ C > 0, ∀ {Ω : Set (Space n)}, IsOpen Ω → Convex ℝ Ω →
      ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω →
      (∀ x ∈ Ω, (hessian u x).PosDef) → AffineMaximalOn Ω u →
      ∀ (L : G ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
        (o : Space n) (c : ℝ) (a : Space n →L[ℝ] ℝ) (b d : ℝ),
      Metric.closedBall (L.symm ((o,c)-v)) r ⊆
        (fun p => L.symm (p-v)) '' sourceEpigraph Ω u →
      a o+b*c+d = q₀ →
      ∀ {K Q : Set (Space n)}, IsCompact K → K ⊆ Ω → MeasurableSet Q → Q ⊆ K →
      (∀ x ∈ Ω, x ∉ K → t₁+ε ≤ graphAffineFunction u a b d x) →
      (∀ x ∈ K, graphAffineFunction u a b d x ∈ Icc t₀ (t₁+ε)) →
      (∀ x ∈ Q, graphAffineFunction u a b d x ≤ t₁-ε) →
      (∀ x ∈ K, ‖L.symm ((x,u x)-v)‖ ≤ R) →
      ENNReal.ofReal (Real.rpow |(L.symm.trans T).toContinuousLinearMap.det|
        ((n:ℝ)/((n:ℝ)+2))) *
        (∫⁻ x in Q, ENNReal.ofReal (affineAreaDensity u x *
          (‖targetGraphConormal u L x‖ * graphInverseMetric u a b d x))) ≤ ENNReal.ofReal C := by
  sorry

end AffineBernstein
end

end OAI
end
