-- Prove2me | Theorems.Thm_OAI_RieszRectifiability_exists_common_height_with_fractional_equation
-- name    : OAI.RieszRectifiability.exists_common_height_with_fractional_equation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:24:37.474477+00:00
-- url     : https://prove2.me/theorems/88abb52e-2fa5-4b74-a343-a0e796d4ca69
-- title:
--   OAI.RieszRectifiability.exists_common_height_with_fractional_equation: intermediate lemma from OpenAI, Riesz transforms and uniform rectifiability in higher codimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Riesz transforms and uniform rectifiability in higher codimension*, OpenAI Math Release, September 24, 2026, result family 81, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RieszRectifiability.exists_common_height_with_fractional_equation` of [lean/OAI/Analysis/RieszRectifiability/Rigidity/DyadicCommonFractionalEquation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Rigidity/DyadicCommonFractionalEquation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RieszRectifiability`, with `open MeasureTheory Metric Set Function Filter Topology SchwartzMap`, `open scoped NNReal ENNReal ContDiff`):
--
--   ```lean
--   theorem exists_common_height_with_fractional_equation {d : ℕ} (p : ℕ)
--       (e : (Fin (p + 1) → ℝ) → Ambient d) (π : Ambient d → Fin (p + 1) → ℝ)
--       (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
--       (a : Ambient d) (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (hplane : e = affinePlaneSection a L)
--       (σ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (σ j)] [∀ j, SFinite (σ j)]
--       (hlocal : CompactTestConvergence σ (coordinatePlaneMeasure e))
--       (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (σ j))
--       (hlower : ∀ j x, x ∈ (σ j).support → ∀ r : ℝ, AdmissibleRadius (σ j) r →
--         ENNReal.ofReal (r ^ (p + 1) / C) ≤ (σ j) (ball x r))
--       (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (σ j).support)
--       (u : ℕ → Ambient d → ℝ) (Ku : ℝ≥0) (hu : ∀ j, LipschitzWith Ku (u j))
--       (z : ℕ → Ambient d) (hz : ∀ j, ‖z j‖ ≤ 1)
--       (hdiff : ∀ j x y, u j x - u j y = inner ℝ (z j) (x - y))
--       (δ A v : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hA : Tendsto A atTop atTop)
--       (hosc : ∀ j, ScalarOscillationBound (p + 1) (σ j) (e 0) (A j) (v j))
--       (hratio : Tendsto (fun j => v j / δ j) atTop (𝓝 0))
--       (W : ℝ) (hW : ∀ j, |u j (e 0)| ≤ W)
--       (hw : ∀ H j, MemLp (fun x => u j x / δ j) 2
--         ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))
--       (B₀ E₀ : ℕ → ℝ)
--       (hB₀ : ∀ H j, (∫ x, (u j x / δ j) ^ 2
--         ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) ≤ B₀ H)
--       (henergy : ∀ H j, Integrable
--         (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) (fun x => u j x / δ j) q.1 q.2)
--         (((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
--           ((σ j).restrict (boundedProjectionRegion π (e 0) K H))))
--       (hE₀ : ∀ H j, (∫ q : Ambient d × Ambient d,
--         fractionalPairEnergy (p + 1) (fun x => u j x / δ j) q.1 q.2
--         ∂(((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
--           ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E₀ H)
--       (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (D b : ℝ) (hb0 : 0 ≤ b) (hb2 : b < 2)
--       (hlast : Tendsto (fun j => ((2 : ℝ) ^ N j)⁻¹ / δ j) atTop (𝓝 0))
--       (hsource : ∀ j l, l ≤ N j → (∫ x in ball (e 0) ((2 : ℝ) ^ l), u j x ^ 2 ∂σ j) ≤
--         δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2) :
--       ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ f : Ambient d → ℝ, Measurable f ∧
--         (∀ H, MemLp f 2 ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
--         (∀ H, Tendsto (fun j => ∫ x, (u (ρ j) x / δ (ρ j)) ^ 2
--           ∂(σ (ρ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
--           (𝓝 (∫ x, f x ^ 2 ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
--         (∀ H (ψ : Ambient d → ℝ) (J B : ℝ≥0), HasCompactSupport ψ →
--           LipschitzWith J ψ → (∀ x, |ψ x| ≤ (B : ℝ)) →
--           Tendsto (fun j => ∫ x, (u (ρ j) x / δ (ρ j)) * ψ x
--             ∂(σ (ρ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
--             (𝓝 (∫ x, f x * ψ x
--               ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
--         (∀ H, Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) f q.1 q.2)
--           (((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
--             ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
--           (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) f q.1 q.2
--             ∂(((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
--               ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E₀ H) ∧
--         (∀ R : ℝ, 0 < R → IntegrableOn
--           (fun x => |f x| * inverseDistancePow (p + 1 + 2) (e 0) x)
--           (closedExterior (e 0) R) (coordinatePlaneMeasure e)) ∧
--         (∀ (φ : Ambient d → ℝ) (J B : ℝ≥0), HasCompactSupport φ → LipschitzWith J φ →
--           (∀ x, |φ x| ≤ (B : ℝ)) → (∫ x, φ x ∂coordinatePlaneMeasure e) = 0 →
--           ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
--             heightPairingOn (p + 1) (coordinatePlaneMeasure e) (e 0) (ball (e 0) R) f φ = 0) ∧
--         (∀ g : 𝓢(Ambient (p + 1), ℂ), (∫ x, g x) = 0 →
--           (∫ x, f (a + L x) • fractionalSchwartzTest p g x) = 0) ∧
--         ∃ T : 𝓢'(Ambient (p + 1), ℂ),
--           (∀ ψ : 𝓢(Ambient (p + 1), ℂ),
--             Integrable (fun x : Ambient (p + 1) => f (a + L x) • ψ x)
--               (volume : Measure (Ambient (p + 1))) ∧
--             T ψ = ∫ x : Ambient (p + 1), f (a + L x) • ψ x) ∧
--           ∀ g : Ambient (p + 1) → ℝ, HasCompactSupport g → ContDiff ℝ ∞ g →
--             ∀ v : Ambient (p + 1), ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
--               heightPairingOn (p + 1) volume (0 : Ambient (p + 1)) (ball 0 R)
--                 (fun x => f (a + L x)) (fun x => fderiv ℝ g x v) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.RieszRectifiability.CompactTestConvergence`, `OAI.RieszRectifiability.GlobalUpperGrowth`, `OAI.RieszRectifiability.ScalarOscillationBound`, `OAI.RieszRectifiability.affinePlaneSection`, `OAI.RieszRectifiability.boundedProjectionRegion`, `OAI.RieszRectifiability.closedExterior`, `OAI.RieszRectifiability.coordinatePlaneMeasure`, `OAI.RieszRectifiability.fractionalPairEnergy`, `OAI.RieszRectifiability.fractionalSchwartzTest`, `OAI.RieszRectifiability.heightPairingOn` and `OAI.RieszRectifiability.inverseDistancePow` (definitions bundle `OAIQ231Rr000` of this split); `OAI.RieszRectifiability.AdmissibleRadius` and `OAI.RieszRectifiability.Ambient` (the published bundle `Def_RieszQuantitative`).
--
--   **Used by.** The proof of `OAI.RieszRectifiability.exists_dyadic_source_excess_limit` of this split imports it.
-- source:
--   OpenAI, Riesz transforms and uniform rectifiability in higher codimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 81; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Rigidity/DyadicCommonFractionalEquation.lean (declaration OAI.RieszRectifiability.exists_common_height_with_fractional_equation)

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

open MeasureTheory Metric Set Function Filter Topology SchwartzMap
open scoped NNReal ENNReal ContDiff

theorem exists_common_height_with_fractional_equation {d : ℕ} (p : ℕ)
    (e : (Fin (p + 1) → ℝ) → Ambient d) (π : Ambient d → Fin (p + 1) → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (a : Ambient d) (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (hplane : e = affinePlaneSection a L)
    (σ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (σ j)] [∀ j, SFinite (σ j)]
    (hlocal : CompactTestConvergence σ (coordinatePlaneMeasure e))
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (σ j))
    (hlower : ∀ j x, x ∈ (σ j).support → ∀ r : ℝ, AdmissibleRadius (σ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (σ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (σ j).support)
    (u : ℕ → Ambient d → ℝ) (Ku : ℝ≥0) (hu : ∀ j, LipschitzWith Ku (u j))
    (z : ℕ → Ambient d) (hz : ∀ j, ‖z j‖ ≤ 1)
    (hdiff : ∀ j x y, u j x - u j y = inner ℝ (z j) (x - y))
    (δ A v : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (σ j) (e 0) (A j) (v j))
    (hratio : Tendsto (fun j => v j / δ j) atTop (𝓝 0))
    (W : ℝ) (hW : ∀ j, |u j (e 0)| ≤ W)
    (hw : ∀ H j, MemLp (fun x => u j x / δ j) 2
      ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))
    (B₀ E₀ : ℕ → ℝ)
    (hB₀ : ∀ H j, (∫ x, (u j x / δ j) ^ 2
      ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) ≤ B₀ H)
    (henergy : ∀ H j, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) (fun x => u j x / δ j) q.1 q.2)
      (((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((σ j).restrict (boundedProjectionRegion π (e 0) K H))))
    (hE₀ : ∀ H j, (∫ q : Ambient d × Ambient d,
      fractionalPairEnergy (p + 1) (fun x => u j x / δ j) q.1 q.2
      ∂(((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E₀ H)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (D b : ℝ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ N j)⁻¹ / δ j) atTop (𝓝 0))
    (hsource : ∀ j l, l ≤ N j → (∫ x in ball (e 0) ((2 : ℝ) ^ l), u j x ^ 2 ∂σ j) ≤
      δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ f : Ambient d → ℝ, Measurable f ∧
      (∀ H, MemLp f 2 ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
      (∀ H, Tendsto (fun j => ∫ x, (u (ρ j) x / δ (ρ j)) ^ 2
        ∂(σ (ρ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
        (𝓝 (∫ x, f x ^ 2 ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
      (∀ H (ψ : Ambient d → ℝ) (J B : ℝ≥0), HasCompactSupport ψ →
        LipschitzWith J ψ → (∀ x, |ψ x| ≤ (B : ℝ)) →
        Tendsto (fun j => ∫ x, (u (ρ j) x / δ (ρ j)) * ψ x
          ∂(σ (ρ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
          (𝓝 (∫ x, f x * ψ x
            ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
      (∀ H, Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) f q.1 q.2)
        (((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
          ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
        (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) f q.1 q.2
          ∂(((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
            ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E₀ H) ∧
      (∀ R : ℝ, 0 < R → IntegrableOn
        (fun x => |f x| * inverseDistancePow (p + 1 + 2) (e 0) x)
        (closedExterior (e 0) R) (coordinatePlaneMeasure e)) ∧
      (∀ (φ : Ambient d → ℝ) (J B : ℝ≥0), HasCompactSupport φ → LipschitzWith J φ →
        (∀ x, |φ x| ≤ (B : ℝ)) → (∫ x, φ x ∂coordinatePlaneMeasure e) = 0 →
        ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
          heightPairingOn (p + 1) (coordinatePlaneMeasure e) (e 0) (ball (e 0) R) f φ = 0) ∧
      (∀ g : 𝓢(Ambient (p + 1), ℂ), (∫ x, g x) = 0 →
        (∫ x, f (a + L x) • fractionalSchwartzTest p g x) = 0) ∧
      ∃ T : 𝓢'(Ambient (p + 1), ℂ),
        (∀ ψ : 𝓢(Ambient (p + 1), ℂ),
          Integrable (fun x : Ambient (p + 1) => f (a + L x) • ψ x)
            (volume : Measure (Ambient (p + 1))) ∧
          T ψ = ∫ x : Ambient (p + 1), f (a + L x) • ψ x) ∧
        ∀ g : Ambient (p + 1) → ℝ, HasCompactSupport g → ContDiff ℝ ∞ g →
          ∀ v : Ambient (p + 1), ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
            heightPairingOn (p + 1) volume (0 : Ambient (p + 1)) (ball 0 R)
              (fun x => f (a + L x)) (fun x => fderiv ℝ g x v) = 0 := by
  sorry

end

end RieszRectifiability

end OAI
end
