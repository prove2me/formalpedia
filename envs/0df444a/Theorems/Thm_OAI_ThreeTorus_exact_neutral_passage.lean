-- Prove2me | Theorems.Thm_OAI_ThreeTorus_exact_neutral_passage
-- name    : OAI.ThreeTorus.exact_neutral_passage
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T12:03:58.25199+00:00
-- url     : https://prove2.me/theorems/fd70f916-10ce-427e-8f83-79679f6febc4
-- title:
--   OAI.ThreeTorus.exact_neutral_passage: intermediate lemma from OpenAI, A smooth three-torus diffeomorphism with simple Lebesgue spectrum
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ThreeTorus.simple_lebesgue_spectrum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A smooth three-torus diffeomorphism with simple Lebesgue spectrum*, OpenAI Math Release, September 23, 2026, result family 144, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ThreeTorus.exact_neutral_passage` of [lean/OAI/Dynamics/ThreeTorus/ThreeTorus/RetainedPackets.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/ThreeTorus/ThreeTorus/RetainedPackets.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ThreeTorus`, with `open MeasureTheory Set Function Filter`, `open scoped Topology BigOperators`):
--
--   ```lean
--   theorem exact_neutral_passage
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
--       (hAs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
--       {v : UnitAddCircle → ℝ} (hv : Measurable v) (hVe : ∀ x : ℝ, v (x:UnitAddCircle) = V x)
--       {B : ℝ} (hB : 0 ≤ B) (hAb : ∀ p, ‖A p‖^2 ≤ B)
--       {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8)
--       {χ : ℝ → UnitAddCircle → ℝ}
--       (hχs : CylinderSmooth χ.uncurry)
--       (hχc : Continuous χ.uncurry) (hcχ : HasCompactSupport χ.uncurry) (hzχ : ∀ a, χ 0 a = 0)
--       (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
--       (hχW : ∀ s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s ≠ 0 → χ s a = 1) :
--       let pold := foldCircleDensity (fun s => ∫ a, stationaryWeight (Icc (l-R) (u+R))
--         (fun x => (m:ℝ)*V x) (A₀ a) s ∂AddCircle.haarAddCircle)
--       ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 < L → ∀ β : ℝ,
--         ∃ S : ℕ → Finset ℤ,
--           (∀ n, 0 < n → ∀ j ∈ S n, j ≠ 0) ∧
--           (∀ n, 0 < n → ∀ j ∉ S n, ∀ a, χ ((j:ℝ)/n) a = 0) ∧
--           ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
--             let ψ := neutralCircleCutoff c
--             let J := neutralJitter c L β
--             let φ := fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)
--             let f := retainedPassage m (H n) A (S n) (fun j => χ ((j:ℝ)/n)) ψ
--             let p := exactRetainedPacketDensity (Ioo δ (1-δ)) (neutralJitterReal c L β)
--               ψ χ m H A (S n) n
--             (∫ x : TripleTorus, ‖packet m A x-f (passageChart (H n) x)‖^2 ∂tripleVolume) <
--               8*δ*B+η ∧
--             (∫ z, |p z-pold z| ∂AddCircle.haarAddCircle) < C/L+4*δ*B+η ∧
--             ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => p x) ∧
--             (∀ k : ℤ, (∫ x : TripleTorus, starRingEnd ℂ (f x)*f (twistIter φ k x) ∂tripleVolume) =
--               ∫ z, (p z:ℂ)*fourier k z ∂AddCircle.haarAddCircle) ∧
--             (∀ j u a, ‖retainedAmplitude ψ χ m H A n j (u,a)‖ =
--               ‖retainedAmplitude ψ χ m H A n j (u,0)‖)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ThreeTorus.CylinderSmooth`, `OAI.ThreeTorus.LawCutoffs`, `OAI.ThreeTorus.TripleTorus`, `OAI.ThreeTorus.exactRetainedPacketDensity`, `OAI.ThreeTorus.foldCircleDensity`, `OAI.ThreeTorus.neutralCircleCutoff`, `OAI.ThreeTorus.neutralJitter`, `OAI.ThreeTorus.neutralJitterReal`, `OAI.ThreeTorus.packet`, `OAI.ThreeTorus.passageChart`, `OAI.ThreeTorus.retainedAmplitude`, `OAI.ThreeTorus.retainedPassage`, `OAI.ThreeTorus.stationaryWeight`, `OAI.ThreeTorus.tripleVolume` and `OAI.ThreeTorus.twistIter` (definitions bundle `OAIQ13Tt000` of this split).
--
--   **Used by.** The proofs of `OAI.ThreeTorus.eventually_colored_controlled_anchor`, `OAI.ThreeTorus.exists_colored_separation_small`, `OAI.ThreeTorus.exists_concrete_colored_controlled_signal` and `OAI.ThreeTorus.exists_two_slow_insertions` of this split import it.
-- source:
--   OpenAI, A smooth three-torus diffeomorphism with simple Lebesgue spectrum, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 144; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-smooth-three-torus-diffeomorphism-with-simple-Lebesgue-spectrum-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/ThreeTorus/ThreeTorus/RetainedPackets.lean (declaration OAI.ThreeTorus.exact_neutral_passage)

import Mathlib
import Definitions.Def_OAIQ13Tt000

section

attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

theorem exact_neutral_passage
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
    (hAs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    {v : UnitAddCircle → ℝ} (hv : Measurable v) (hVe : ∀ x : ℝ, v (x:UnitAddCircle) = V x)
    {B : ℝ} (hB : 0 ≤ B) (hAb : ∀ p, ‖A p‖^2 ≤ B)
    {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8)
    {χ : ℝ → UnitAddCircle → ℝ}
    (hχs : CylinderSmooth χ.uncurry)
    (hχc : Continuous χ.uncurry) (hcχ : HasCompactSupport χ.uncurry) (hzχ : ∀ a, χ 0 a = 0)
    (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s ≠ 0 → χ s a = 1) :
    let pold := foldCircleDensity (fun s => ∫ a, stationaryWeight (Icc (l-R) (u+R))
      (fun x => (m:ℝ)*V x) (A₀ a) s ∂AddCircle.haarAddCircle)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 < L → ∀ β : ℝ,
      ∃ S : ℕ → Finset ℤ,
        (∀ n, 0 < n → ∀ j ∈ S n, j ≠ 0) ∧
        (∀ n, 0 < n → ∀ j ∉ S n, ∀ a, χ ((j:ℝ)/n) a = 0) ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
          let ψ := neutralCircleCutoff c
          let J := neutralJitter c L β
          let φ := fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)
          let f := retainedPassage m (H n) A (S n) (fun j => χ ((j:ℝ)/n)) ψ
          let p := exactRetainedPacketDensity (Ioo δ (1-δ)) (neutralJitterReal c L β)
            ψ χ m H A (S n) n
          (∫ x : TripleTorus, ‖packet m A x-f (passageChart (H n) x)‖^2 ∂tripleVolume) <
            8*δ*B+η ∧
          (∫ z, |p z-pold z| ∂AddCircle.haarAddCircle) < C/L+4*δ*B+η ∧
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => p x) ∧
          (∀ k : ℤ, (∫ x : TripleTorus, starRingEnd ℂ (f x)*f (twistIter φ k x) ∂tripleVolume) =
            ∫ z, (p z:ℂ)*fourier k z ∂AddCircle.haarAddCircle) ∧
          (∀ j u a, ‖retainedAmplitude ψ χ m H A n j (u,a)‖ =
            ‖retainedAmplitude ψ χ m H A n j (u,0)‖) := by
  sorry

end ThreeTorus
end
end

end OAI
end
