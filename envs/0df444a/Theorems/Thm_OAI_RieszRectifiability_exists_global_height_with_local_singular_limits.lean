-- Prove2me | Theorems.Thm_OAI_RieszRectifiability_exists_global_height_with_local_singular_limits
-- name    : OAI.RieszRectifiability.exists_global_height_with_local_singular_limits
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:24:21.48053+00:00
-- url     : https://prove2.me/theorems/8b410fe0-0d37-4c55-89cd-731e3857a397
-- title:
--   OAI.RieszRectifiability.exists_global_height_with_local_singular_limits: intermediate lemma from OpenAI, Riesz transforms and uniform rectifiability in higher codimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Riesz transforms and uniform rectifiability in higher codimension*, OpenAI Math Release, September 24, 2026, result family 81, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RieszRectifiability.exists_global_height_with_local_singular_limits` of [lean/OAI/Analysis/RieszRectifiability/Kernel/GlobalSingularHeight.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Kernel/GlobalSingularHeight.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RieszRectifiability`, with `open BoxIntegral MeasureTheory Metric Set Function Filter Topology`, `open scoped NNReal ENNReal`):
--
--   ```lean
--   theorem exists_global_height_with_local_singular_limits {d : ℕ} (p : ℕ)
--       (e : (Fin (p + 1) → ℝ) → Ambient d) (π : Ambient d → Fin (p + 1) → ℝ)
--       (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
--       (σ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (σ j)]
--       (hlocal : CompactTestConvergence σ (coordinatePlaneMeasure e))
--       (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (σ j))
--       (hlower : ∀ j x, x ∈ (σ j).support → ∀ r : ℝ, AdmissibleRadius (σ j) r →
--         ENNReal.ofReal (r ^ (p + 1) / C) ≤ (σ j) (ball x r))
--       (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (σ j).support)
--       (w : ℕ → Ambient d → ℝ) (hwm : ∀ j, Measurable (w j))
--       (hw : ∀ H j, MemLp (w j) 2 ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))
--       (B E : ℕ → ℝ)
--       (hB : ∀ H j, (∫ x, w j x ^ 2 ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) ≤ B H)
--       (henergy : ∀ H j, Integrable
--         (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) (w j) q.1 q.2)
--         (((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
--           ((σ j).restrict (boundedProjectionRegion π (e 0) K H))))
--       (hE : ∀ H j, (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) (w j) q.1 q.2
--         ∂(((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
--           ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E H) :
--       ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : Ambient d → ℝ, Measurable f ∧
--         (∀ H, MemLp f 2 ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
--         (∀ H, Tendsto (fun j => ∫ x, w (φ j) x ^ 2
--           ∂(σ (φ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
--           (𝓝 (∫ x, f x ^ 2 ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
--         (∀ H (ψ : Ambient d → ℝ) (L A : ℝ≥0), HasCompactSupport ψ →
--           LipschitzWith L ψ → (∀ x, |ψ x| ≤ (A : ℝ)) →
--           Tendsto (fun j => ∫ x, w (φ j) x * ψ x
--             ∂(σ (φ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
--             (𝓝 (∫ x, f x * ψ x
--               ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
--         ∀ H, Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) f q.1 q.2)
--           (((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
--             ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
--           (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) f q.1 q.2
--             ∂(((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
--               ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E H ∧
--           ∀ (ψ : Ambient d → ℝ) (L A : ℝ≥0), LipschitzWith L ψ → (∀ x, |ψ x| ≤ (A : ℝ)) →
--             Tendsto (fun j => ∫ q : Ambient d × Ambient d,
--               fractionalBilinear (p + 1) (w (φ j)) ψ q.1 q.2
--               ∂(((σ (φ j)).restrict (boundedProjectionRegion π (e 0) K H)).prod
--                 ((σ (φ j)).restrict (boundedProjectionRegion π (e 0) K H)))) atTop
--               (𝓝 (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) f ψ q.1 q.2
--                 ∂(((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
--                   ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RieszRectifiability.CompactTestConvergence`, `OAI.RieszRectifiability.GlobalUpperGrowth`, `OAI.RieszRectifiability.boundedProjectionRegion`, `OAI.RieszRectifiability.coordinatePlaneMeasure`, `OAI.RieszRectifiability.fractionalBilinear` and `OAI.RieszRectifiability.fractionalPairEnergy` (definitions bundle `OAIQ231Rr000` of this split); `OAI.RieszRectifiability.AdmissibleRadius` and `OAI.RieszRectifiability.Ambient` (the published bundle `Def_RieszQuantitative`).
--
--   **Used by.** The proof of `OAI.RieszRectifiability.exists_common_height_with_fractional_equation` of this split imports it.
-- source:
--   OpenAI, Riesz transforms and uniform rectifiability in higher codimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 81; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Kernel/GlobalSingularHeight.lean (declaration OAI.RieszRectifiability.exists_global_height_with_local_singular_limits)

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem exists_global_height_with_local_singular_limits {d : ℕ} (p : ℕ)
    (e : (Fin (p + 1) → ℝ) → Ambient d) (π : Ambient d → Fin (p + 1) → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (σ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (σ j)]
    (hlocal : CompactTestConvergence σ (coordinatePlaneMeasure e))
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (σ j))
    (hlower : ∀ j x, x ∈ (σ j).support → ∀ r : ℝ, AdmissibleRadius (σ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (σ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (σ j).support)
    (w : ℕ → Ambient d → ℝ) (hwm : ∀ j, Measurable (w j))
    (hw : ∀ H j, MemLp (w j) 2 ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))
    (B E : ℕ → ℝ)
    (hB : ∀ H j, (∫ x, w j x ^ 2 ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) ≤ B H)
    (henergy : ∀ H j, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) (w j) q.1 q.2)
      (((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((σ j).restrict (boundedProjectionRegion π (e 0) K H))))
    (hE : ∀ H j, (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) (w j) q.1 q.2
      ∂(((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E H) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : Ambient d → ℝ, Measurable f ∧
      (∀ H, MemLp f 2 ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
      (∀ H, Tendsto (fun j => ∫ x, w (φ j) x ^ 2
        ∂(σ (φ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
        (𝓝 (∫ x, f x ^ 2 ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
      (∀ H (ψ : Ambient d → ℝ) (L A : ℝ≥0), HasCompactSupport ψ →
        LipschitzWith L ψ → (∀ x, |ψ x| ≤ (A : ℝ)) →
        Tendsto (fun j => ∫ x, w (φ j) x * ψ x
          ∂(σ (φ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
          (𝓝 (∫ x, f x * ψ x
            ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
      ∀ H, Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) f q.1 q.2)
        (((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
          ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
        (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) f q.1 q.2
          ∂(((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
            ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E H ∧
        ∀ (ψ : Ambient d → ℝ) (L A : ℝ≥0), LipschitzWith L ψ → (∀ x, |ψ x| ≤ (A : ℝ)) →
          Tendsto (fun j => ∫ q : Ambient d × Ambient d,
            fractionalBilinear (p + 1) (w (φ j)) ψ q.1 q.2
            ∂(((σ (φ j)).restrict (boundedProjectionRegion π (e 0) K H)).prod
              ((σ (φ j)).restrict (boundedProjectionRegion π (e 0) K H)))) atTop
            (𝓝 (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) f ψ q.1 q.2
              ∂(((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
                ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))))) := by
  sorry

end

end RieszRectifiability

end OAI
end
