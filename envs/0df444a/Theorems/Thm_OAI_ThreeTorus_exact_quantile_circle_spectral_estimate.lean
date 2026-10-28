-- Prove2me | Theorems.Thm_OAI_ThreeTorus_exact_quantile_circle_spectral_estimate
-- name    : OAI.ThreeTorus.exact_quantile_circle_spectral_estimate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T12:03:36.303839+00:00
-- url     : https://prove2.me/theorems/77448fd0-8920-425b-90ed-710700839a87
-- title:
--   OAI.ThreeTorus.exact_quantile_circle_spectral_estimate: intermediate lemma from OpenAI, A smooth three-torus diffeomorphism with simple Lebesgue spectrum
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ThreeTorus.simple_lebesgue_spectrum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A smooth three-torus diffeomorphism with simple Lebesgue spectrum*, OpenAI Math Release, September 23, 2026, result family 144, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ThreeTorus.exact_quantile_circle_spectral_estimate` of [lean/OAI/Dynamics/ThreeTorus/ThreeTorus/Transmission.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/ThreeTorus/ThreeTorus/Transmission.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ThreeTorus`, with `open MeasureTheory Filter Set Complex`, `open scoped Topology SchwartzMap FourierTransform Real`, `open scoped Topology`, `open MeasureTheory Set`, `open scoped ENNReal Topology`, `open Set Function Filter`, `open scoped Topology NNReal`, `open MeasureTheory Filter Set`, `open MeasureTheory Set Function`, `open scoped Topology ENNReal`, `open scoped Topology BigOperators`, `open MeasureTheory Set Filter`, `open scoped Topology FourierTransform`, `open MeasureTheory Set Filter Asymptotics`, `open MeasureTheory Set Filter Function`, `open MeasureTheory Set Filter Function`, `open scoped Topology BigOperators FourierTransform`):
--
--   ```lean
--   theorem exact_quantile_circle_spectral_estimate
--       {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
--       {Pr V : ℝ → ℝ} {m : ℤ} {Δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
--       {o l u R : ℝ}
--       (hm : m ≠ 0)
--       (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(Pr x+Δ n*x) : UnitAddCircle))
--       (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
--       (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
--       (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
--       (hAr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
--         (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1))
--       (hsupp : ∀ a, support (A₀ a) ⊆ Ioc l u)
--       (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
--       (hPr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Pr)
--       (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv Pr = V)
--       (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
--       (h0 : 0 ∉ (fun x => (m:ℝ)*V x) '' Icc l u)
--       (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hΔt : Tendsto Δ atTop (𝓝 0))
--       (hmod : ∀ a x, ‖A₀ a x‖ = ‖A₀ 0 x‖)
--       {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
--       (hp : ∀ y, 0 < ρ y) (hρm : ∫ y, ρ y = 1)
--       {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, |ρ y| ≤ C/(1+y^2)) {D : ℝ}
--       (hF : ∀ v, D < |v| → 𝓕 (fun y => (ρ y : ℂ)) v = 0)
--       {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8)
--       {χ : ℝ → UnitAddCircle → ℝ}
--       (hχc : Continuous χ.uncurry) (hcχ : HasCompactSupport χ.uncurry) (hzχ : ∀ a, χ 0 a = 0)
--       (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
--       (hχW : ∀ s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s ≠ 0 → χ s a = 1)
--       {g : UnitAddCircle → ℝ} (hg : Continuous g) {ε : ℝ}
--       (hideal : ∀ s ∈ support (stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ 0)),
--         ∀ y, |foldCircleDensity (scaledDensity ρ s) y-g y| ≤ ε)
--       {η : ℝ} (hη : 0 < η) :
--       let w := stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ 0)
--       ∃ S : ℕ → Finset ℤ,
--         (∀ n, 0 < n → ∀ j ∈ S n, j ≠ 0) ∧
--         (∀ n, 0 < n → ∀ j ∉ S n, ∀ a, χ ((j:ℝ)/n) a = 0) ∧
--         ∀ᶠ n : ℕ in atTop, (∫ z,
--           |exactRetainedPacketDensity (Ioo δ (1-δ)) (lawJitter ρ c) (neutralCircleCutoff c)
--             χ m H A (S n) n z - foldCircleDensity w z*g ((n:ℤ) • z)| ∂AddCircle.haarAddCircle) <
--           (∫ s, w s)*(4*δ+ε)+η
--   ```
--
--   **Definitions.** The statement is written with `OAI.ThreeTorus.LawCutoffs`, `OAI.ThreeTorus.exactRetainedPacketDensity`, `OAI.ThreeTorus.foldCircleDensity`, `OAI.ThreeTorus.lawJitter`, `OAI.ThreeTorus.neutralCircleCutoff`, `OAI.ThreeTorus.scaledDensity` and `OAI.ThreeTorus.stationaryWeight` (definitions bundle `OAIQ13Tt000` of this split).
--
--   **Used by.** The proof of `OAI.ThreeTorus.exact_quantile_passage` of this split imports it.
-- source:
--   OpenAI, A smooth three-torus diffeomorphism with simple Lebesgue spectrum, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 144; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-smooth-three-torus-diffeomorphism-with-simple-Lebesgue-spectrum-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/ThreeTorus/ThreeTorus/Transmission.lean (declaration OAI.ThreeTorus.exact_quantile_circle_spectral_estimate)

import Mathlib
import Definitions.Def_OAIQ13Tt000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal
open scoped Topology BigOperators
open MeasureTheory Set Filter
open scoped Topology FourierTransform
open MeasureTheory Set Filter Asymptotics
open MeasureTheory Set Filter Function

namespace ThreeTorus
open MeasureTheory Set Filter Function
open scoped Topology BigOperators FourierTransform

theorem exact_quantile_circle_spectral_estimate
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {Pr V : ℝ → ℝ} {m : ℤ} {Δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : m ≠ 0)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(Pr x+Δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hAr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1))
    (hsupp : ∀ a, support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hPr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Pr)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv Pr = V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (h0 : 0 ∉ (fun x => (m:ℝ)*V x) '' Icc l u)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hΔt : Tendsto Δ atTop (𝓝 0))
    (hmod : ∀ a x, ‖A₀ a x‖ = ‖A₀ 0 x‖)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hρm : ∫ y, ρ y = 1)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, |ρ y| ≤ C/(1+y^2)) {D : ℝ}
    (hF : ∀ v, D < |v| → 𝓕 (fun y => (ρ y : ℂ)) v = 0)
    {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8)
    {χ : ℝ → UnitAddCircle → ℝ}
    (hχc : Continuous χ.uncurry) (hcχ : HasCompactSupport χ.uncurry) (hzχ : ∀ a, χ 0 a = 0)
    (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s ≠ 0 → χ s a = 1)
    {g : UnitAddCircle → ℝ} (hg : Continuous g) {ε : ℝ}
    (hideal : ∀ s ∈ support (stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ 0)),
      ∀ y, |foldCircleDensity (scaledDensity ρ s) y-g y| ≤ ε)
    {η : ℝ} (hη : 0 < η) :
    let w := stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ 0)
    ∃ S : ℕ → Finset ℤ,
      (∀ n, 0 < n → ∀ j ∈ S n, j ≠ 0) ∧
      (∀ n, 0 < n → ∀ j ∉ S n, ∀ a, χ ((j:ℝ)/n) a = 0) ∧
      ∀ᶠ n : ℕ in atTop, (∫ z,
        |exactRetainedPacketDensity (Ioo δ (1-δ)) (lawJitter ρ c) (neutralCircleCutoff c)
          χ m H A (S n) n z - foldCircleDensity w z*g ((n:ℤ) • z)| ∂AddCircle.haarAddCircle) <
        (∫ s, w s)*(4*δ+ε)+η := by
  sorry

end ThreeTorus

end

end OAI
end
