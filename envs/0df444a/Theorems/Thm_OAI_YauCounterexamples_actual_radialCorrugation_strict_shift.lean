-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_actual_radialCorrugation_strict_shift
-- name    : OAI.YauCounterexamples.actual_radialCorrugation_strict_shift
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:31:58.804204+00:00
-- url     : https://prove2.me/theorems/47d91d70-dd1d-4e5f-89a0-adcf4aefccfe
-- title:
--   OAI.YauCounterexamples.actual_radialCorrugation_strict_shift: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.actual_radialCorrugation_strict_shift` of [lean/OAI/Geometry/SmoothYau/Estimates/ActualRadialCorrugationStrictShift.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/ActualRadialCorrugationStrictShift.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Metric`, `open scoped Topology ContDiff InnerProductSpace`):
--
--   ```lean
--   theorem actual_radialCorrugation_strict_shift
--       (K₀ : Set E) (hK₀ : IsCompact K₀) {V : K₀ → Type*}
--       [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
--       [∀ x, FiniteDimensional ℝ (V x)] (hd : ∀ x, 3 ≤ Module.finrank ℝ (V x))
--       (j : ∀ x, V x →L[ℝ] E) (J : ℝ) (hJ : 0 ≤ J) (hj : ∀ x, ‖j x‖ ≤ J)
--       (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : Continuous Γ)
--       {ψ χ : E → ℝ} {y : E → ProfilePlane}
--       (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ) (hy : ContDiff ℝ ∞ y)
--       (hχs : HasCompactSupport χ) (hχv : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
--       {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 0)
--       (hβv : ∀ t, 0 ≤ β t ∧ β t ≤ 1)
--       {b r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hsmallR : 2*R < 1)
--       (hb : b ≤ r^2) (hzero : ∀ t, b ≤ t → β t = 0)
--       (Fmax K S : ℝ) (hFmax : 0 ≤ Fmax) (hK : 0 ≤ K) (hS : 0 ≤ S)
--       (hcoef : ∀ z, 0 ≤ periodicRadialSpeed β R z ∧ periodicRadialSpeed β R z ≤ Fmax ∧
--         (periodicRadialSpeed β R z)^2 ≤ S*periodicAngularSecond β R z ∧
--         |periodicRadialSecond β R z| ≤ K)
--       (m α M Hmax δ A : ℝ)
--       (hm : 0 < m) (hm1 : m ≤ 1) (hα : 0 < α) (hM : 0 ≤ M) (hHmax : 0 ≤ Hmax)
--       (hδ : 0 < δ) (hA : 0 < A) (hsmall : 9216*K*S*δ^2 ≤ 1)
--       (ha0 : ∀ x, α ≤ ‖pulledGradient (j x) ψ x‖)
--       (haM : ∀ x, ‖pulledGradient (j x) ψ x‖ ≤ M)
--       (hHH : ∀ x, ‖pulledHessian Γ (j x) ψ x‖ ≤ Hmax)
--       (hAa : ∀ x, A ≤ 2*‖pulledGradient (j x) ψ x‖)
--       (hmargin : ∀ x w, ‖w‖ = 1 → inner ℝ (pulledGradient (j x) ψ x) w = 0 →
--         m ≤ profileTrace (pulledHessian Γ (j x) ψ x) (pulledGradient (j x) ψ x) w)
--       (hfirst : ∀ x : K₀, fderiv ℝ y x (j x (pulledGradient (j x) ψ x)) = 0)
--       (hup : ∀ (x : K₀) v, Real.sqrt ((fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2) ≤ 2*‖v‖)
--       (hlo : ∀ (x : K₀) v, inner ℝ (pulledGradient (j x) ψ x) v = 0 →
--         ‖v‖/2 ≤ Real.sqrt ((fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2)) :
--       ∀ᶠ N : ℕ in atTop, ∀ d : ProfilePlane, ∀ x : K₀,
--         profileStrict (pulledHessian Γ (j x) (radialCorrugation ψ χ (fun z => y z+d) β b δ A N) x)
--           (pulledGradient (j x) (radialCorrugation ψ χ (fun z => y z+d) β b δ A N) x) ∧
--         pulledGradient (j x) (radialCorrugation ψ χ (fun z => y z+d) β b δ A N) x ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ProfileForm`, `OAI.YauCounterexamples.ProfilePlane`, `OAI.YauCounterexamples.periodicAngularSecond`, `OAI.YauCounterexamples.periodicRadialSecond` and `OAI.YauCounterexamples.periodicRadialSpeed` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.pulledGradient` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.profileStrict`, `OAI.YauCounterexamples.profileTrace`, `OAI.YauCounterexamples.pulledHessian` and `OAI.YauCounterexamples.radialCorrugation` (definitions bundle `OAIQ070A007` of this split).
--
--   **Used by.** The proofs of `OAI.YauCounterexamples.actual_metric_radial_finite` and `OAI_YauCounterexamples_actual_metric_radial_patch_shift` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/ActualRadialCorrugationStrictShift.lean (declaration OAI.YauCounterexamples.actual_radialCorrugation_strict_shift)

import Mathlib
import Definitions.Def_OAIQ070A007

section

attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace YauCounterexamples
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem actual_radialCorrugation_strict_shift
    (K₀ : Set E) (hK₀ : IsCompact K₀) {V : K₀ → Type*}
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [∀ x, FiniteDimensional ℝ (V x)] (hd : ∀ x, 3 ≤ Module.finrank ℝ (V x))
    (j : ∀ x, V x →L[ℝ] E) (J : ℝ) (hJ : 0 ≤ J) (hj : ∀ x, ‖j x‖ ≤ J)
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : Continuous Γ)
    {ψ χ : E → ℝ} {y : E → ProfilePlane}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ) (hy : ContDiff ℝ ∞ y)
    (hχs : HasCompactSupport χ) (hχv : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 0)
    (hβv : ∀ t, 0 ≤ β t ∧ β t ≤ 1)
    {b r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hsmallR : 2*R < 1)
    (hb : b ≤ r^2) (hzero : ∀ t, b ≤ t → β t = 0)
    (Fmax K S : ℝ) (hFmax : 0 ≤ Fmax) (hK : 0 ≤ K) (hS : 0 ≤ S)
    (hcoef : ∀ z, 0 ≤ periodicRadialSpeed β R z ∧ periodicRadialSpeed β R z ≤ Fmax ∧
      (periodicRadialSpeed β R z)^2 ≤ S*periodicAngularSecond β R z ∧
      |periodicRadialSecond β R z| ≤ K)
    (m α M Hmax δ A : ℝ)
    (hm : 0 < m) (hm1 : m ≤ 1) (hα : 0 < α) (hM : 0 ≤ M) (hHmax : 0 ≤ Hmax)
    (hδ : 0 < δ) (hA : 0 < A) (hsmall : 9216*K*S*δ^2 ≤ 1)
    (ha0 : ∀ x, α ≤ ‖pulledGradient (j x) ψ x‖)
    (haM : ∀ x, ‖pulledGradient (j x) ψ x‖ ≤ M)
    (hHH : ∀ x, ‖pulledHessian Γ (j x) ψ x‖ ≤ Hmax)
    (hAa : ∀ x, A ≤ 2*‖pulledGradient (j x) ψ x‖)
    (hmargin : ∀ x w, ‖w‖ = 1 → inner ℝ (pulledGradient (j x) ψ x) w = 0 →
      m ≤ profileTrace (pulledHessian Γ (j x) ψ x) (pulledGradient (j x) ψ x) w)
    (hfirst : ∀ x : K₀, fderiv ℝ y x (j x (pulledGradient (j x) ψ x)) = 0)
    (hup : ∀ (x : K₀) v, Real.sqrt ((fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2) ≤ 2*‖v‖)
    (hlo : ∀ (x : K₀) v, inner ℝ (pulledGradient (j x) ψ x) v = 0 →
      ‖v‖/2 ≤ Real.sqrt ((fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2)) :
    ∀ᶠ N : ℕ in atTop, ∀ d : ProfilePlane, ∀ x : K₀,
      profileStrict (pulledHessian Γ (j x) (radialCorrugation ψ χ (fun z => y z+d) β b δ A N) x)
        (pulledGradient (j x) (radialCorrugation ψ χ (fun z => y z+d) β b δ A N) x) ∧
      pulledGradient (j x) (radialCorrugation ψ χ (fun z => y z+d) β b δ A N) x ≠ 0 := by
  sorry

end
end YauCounterexamples

end OAI
end
