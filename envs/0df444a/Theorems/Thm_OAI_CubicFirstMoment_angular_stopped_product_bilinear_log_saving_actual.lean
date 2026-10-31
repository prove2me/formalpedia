-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_angular_stopped_product_bilinear_log_saving_actual
-- name    : OAI.CubicFirstMoment.angular_stopped_product_bilinear_log_saving_actual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:57:36.033521+00:00
-- url     : https://prove2.me/theorems/ff9b5835-0a64-4958-8a6c-25dc0ccddf1e
-- title:
--   OAI.CubicFirstMoment.angular_stopped_product_bilinear_log_saving_actual: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.angular_stopped_product_bilinear_log_saving_actual` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralAngularStoppedProductLogSaving.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralAngularStoppedProductLogSaving.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter MeasureTheory`, `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem angular_stopped_product_bilinear_log_saving_actual
--       (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
--       (ℓ : ℤ) (hℓ : ℓ ≠ 0)
--       {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hHuxley : HuxleyAdditiveLargeSieve)
--       (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
--         AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
--       {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
--       (hF : 0 ≤ F) (hJ : 0 ≤ J)
--       (Φ : ℝ → ℝ) (hΦnn : ∀ x, 0 ≤ Φ x)
--       (hΦ : HasCompactSupport (fun x => (Φ x:ℂ)))
--       (hΦpos : tsupport (fun x => (Φ x:ℂ)) ⊆ Set.Ioi 0)
--       (hΦ' : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)))
--       (hΦone : ∀ x ∈ Set.Icc (1:ℝ) 2, 1 ≤ Φ x)
--       {RΦ : ℝ} (hcut : ∀ x, RΦ < x → Φ x = 0)
--       (Ω : ℝ → ℂ) (hΩ : HasCompactSupport Ω) (hΩpos : tsupport Ω ⊆ Set.Ioi 0)
--       (hΩsm : ContDiff ℝ ∞ Ω) (k H : ℕ) :
--       ∃ (d G : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
--         ∀ (δ b u v A X₀ : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
--         2 ≤ b → X^κ ≤ b → b ≤ X → 0 < X₀ →
--         0 ≤ v → |u| ≤ (Real.log X)^H → 1+v ≤ (Real.log X)^F →
--         ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
--         (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ v) →
--         2*b^(3/2:ℝ) ≤ A → A ≤ b^2/(Real.log X)^(15*(2*k+d)) →
--         ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
--         ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
--         2*(Real.log X)^G ≤ min (X^ξ) (geometricBinLower (1+δ) X h) →
--         ∀ (E₀ U P : Finset Eisenstein) (ψ : ℝ → ℝ) (w : ℝ)
--           (remaining : Eisenstein → Prop),
--         (∀ c ∈ E₀, primary c) → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
--         (∀ c ∈ P, primary c ∧ Squarefree c ∧ A ≤ norm c ∧ norm c ≤ 2*A) →
--         let S := stoppedIntervalSupport ι X (b/2) b e
--         let β := angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
--           (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
--             j₀ k₀ h Z Q early)
--         ‖centeredProductSmoothed P S (angularStoppedAlpha ℓ E₀ U ψ w remaining) β 0 Ω X₀ u‖ ≤
--           K*A^(5/6:ℝ)*b^(5/6:ℝ)/(Real.log X)^k
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.AngularGammaQuotientStripBound` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.MontgomeryVaughanBound` and `OAI.CubicFirstMoment.geometricBinLower` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.metaplecticAngularShift` (definitions bundle `OAIQ096A003` of this split); `OAI.CubicFirstMoment.AngularKummerPrimeExplicitEstimate` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve` and `OAI.CubicFirstMoment.PrimaryPrimePNT` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.angularStoppedAlpha`, `OAI.CubicFirstMoment.angularStoppedRowCoefficient`, `OAI.CubicFirstMoment.centeredProductSmoothed`, `OAI.CubicFirstMoment.geometricPrimeBin`, `OAI.CubicFirstMoment.stoppedIntervalSupport` and `OAI.CubicFirstMoment.stoppedSideTest` (definitions bundle `OAIQ096A008` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI_CubicFirstMoment_angular_distinguishedStoppedDyad_early_bound_actual` and `OAI.CubicFirstMoment.angular_scaleFirstStoppedEarly_isLittleO_actual` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralAngularStoppedProductLogSaving.lean (declaration OAI.CubicFirstMoment.angular_stopped_product_bilinear_log_saving_actual)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A007
import Definitions.Def_OAIQ096A008

section

attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_product_bilinear_log_saving_actual
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (Φ : ℝ → ℝ) (hΦnn : ∀ x, 0 ≤ Φ x)
    (hΦ : HasCompactSupport (fun x => (Φ x:ℂ)))
    (hΦpos : tsupport (fun x => (Φ x:ℂ)) ⊆ Set.Ioi 0)
    (hΦ' : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)))
    (hΦone : ∀ x ∈ Set.Icc (1:ℝ) 2, 1 ≤ Φ x)
    {RΦ : ℝ} (hcut : ∀ x, RΦ < x → Φ x = 0)
    (Ω : ℝ → ℂ) (hΩ : HasCompactSupport Ω) (hΩpos : tsupport Ω ⊆ Set.Ioi 0)
    (hΩsm : ContDiff ℝ ∞ Ω) (k H : ℕ) :
    ∃ (d G : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b u v A X₀ : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X → 0 < X₀ →
      0 ≤ v → |u| ≤ (Real.log X)^H → 1+v ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ v) →
      2*b^(3/2:ℝ) ≤ A → A ≤ b^2/(Real.log X)^(15*(2*k+d)) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2*(Real.log X)^G ≤ min (X^ξ) (geometricBinLower (1+δ) X h) →
      ∀ (E₀ U P : Finset Eisenstein) (ψ : ℝ → ℝ) (w : ℝ)
        (remaining : Eisenstein → Prop),
      (∀ c ∈ E₀, primary c) → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      (∀ c ∈ P, primary c ∧ Squarefree c ∧ A ≤ norm c ∧ norm c ≤ 2*A) →
      let S := stoppedIntervalSupport ι X (b/2) b e
      let β := angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early)
      ‖centeredProductSmoothed P S (angularStoppedAlpha ℓ E₀ U ψ w remaining) β 0 Ω X₀ u‖ ≤
        K*A^(5/6:ℝ)*b^(5/6:ℝ)/(Real.log X)^k := by
  sorry

end CubicFirstMoment

end

end OAI
end
