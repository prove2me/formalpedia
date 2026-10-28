-- Prove2me | Theorems.Thm_OAI_ThreeTorus_exact_neutral_circle_spectral_estimate
-- name    : OAI.ThreeTorus.exact_neutral_circle_spectral_estimate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T12:02:36.955207+00:00
-- url     : https://prove2.me/theorems/d15c6066-57ec-41e6-8a3c-05bdcc4138b0
-- title:
--   OAI.ThreeTorus.exact_neutral_circle_spectral_estimate: intermediate lemma from OpenAI, A smooth three-torus diffeomorphism with simple Lebesgue spectrum
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ThreeTorus.simple_lebesgue_spectrum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A smooth three-torus diffeomorphism with simple Lebesgue spectrum*, OpenAI Math Release, September 23, 2026, result family 144, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ThreeTorus.exact_neutral_circle_spectral_estimate` of [lean/OAI/Dynamics/ThreeTorus/ThreeTorus/NeutralSupport.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/ThreeTorus/ThreeTorus/NeutralSupport.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ThreeTorus`, with `open MeasureTheory Set Filter`, `open scoped Topology`, `open MeasureTheory Set Function Filter`, `open scoped Topology NNReal`):
--
--   ```lean
--   lemma exact_neutral_circle_spectral_estimate
--       {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
--       {Pr V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
--       {o l u R : ℝ}
--       (hm : m ≠ 0)
--       (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(Pr x+δ n*x) : UnitAddCircle))
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
--       (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hδt : Tendsto δ atTop (𝓝 0))
--       {I : Set ℝ} {o' : ℝ}
--       {χ : ℝ → UnitAddCircle → ℝ} {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
--       (hIo : IsOpen I)
--       (hψ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hcψ₀ : HasCompactSupport ψ₀)
--       (hsψ₀ : tsupport ψ₀ ⊆ Ioc o' (o'+1) ∩ I)
--       (heψ : ∀ x ∈ Ioc o' (o'+1), ψ₀ x = ψ (x : UnitAddCircle))
--       (hψc : Continuous ψ) (hχc : Continuous χ.uncurry) (hcχ : HasCompactSupport χ.uncurry)
--       (hzχ : ∀ a, χ 0 a = 0)
--       (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1) (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
--       (hχW : ∀ s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s ≠ 0 → χ s a = 1)
--       {Q : ℕ} (hQ : 0 < Q) (h : ℤ) :
--       let F := stationaryCutoffLift (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
--         (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1) ψ₀
--       ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 < L → ∀ β : ℝ,
--         ∀ (J₀ : ℝ → ℝ) (J : UnitAddCircle → ℝ),
--         (∀ a ∈ I, J₀ a = L*a+β) →
--         ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀ → Measurable J →
--         (∀ x ∈ I, J (x : UnitAddCircle) = J₀ x) →
--         ∃ S : ℕ → Finset ℤ,
--           (∀ n, 0 < n → ∀ k ∈ S n, h+k*(Q:ℤ) ≠ 0) ∧
--           (∀ n, 0 < n → ∀ k ∉ S n, ∀ a, χ (((h+k*(Q:ℤ):ℤ):ℝ)/n) a = 0) ∧
--           ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
--             (∫ a, |foldCircleDensity (fun t => ∑ k ∈ S n,
--               unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
--                 (circleDensityLift o' (retainedCircleWeight ψ χ
--                   (fun n j => exactPassageCoeff m (H n) A j) n (h+k*(Q:ℤ))))
--                 n ((h+k*(Q:ℤ):ℤ):ℝ) t) a-
--               foldCircleDensity (fun s => (Q:ℝ)⁻¹*(∫ a, F (a,s))) a|
--               ∂AddCircle.haarAddCircle) < C/L+η
--   ```
--
--   **Definitions.** The statement is written with `OAI.ThreeTorus.circleDensityLift`, `OAI.ThreeTorus.exactPassageCoeff`, `OAI.ThreeTorus.foldCircleDensity`, `OAI.ThreeTorus.retainedCircleWeight`, `OAI.ThreeTorus.stationaryCutoffLift`, `OAI.ThreeTorus.stationaryWeight` and `OAI.ThreeTorus.unfoldedModeDensity` (definitions bundle `OAIQ13Tt000` of this split).
--
--   **Used by.** The proofs of `OAI.ThreeTorus.eventually_colored_controlled_anchor`, `OAI.ThreeTorus.exact_neutral_passage` and `OAI.ThreeTorus.exists_concrete_colored_controlled_signal` of this split import it.
-- source:
--   OpenAI, A smooth three-torus diffeomorphism with simple Lebesgue spectrum, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 144; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-smooth-three-torus-diffeomorphism-with-simple-Lebesgue-spectrum-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/ThreeTorus/ThreeTorus/NeutralSupport.lean (declaration OAI.ThreeTorus.exact_neutral_circle_spectral_estimate)

import Mathlib
import Definitions.Def_OAIQ13Tt000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology NNReal

lemma exact_neutral_circle_spectral_estimate
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {Pr V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : m ≠ 0)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(Pr x+δ n*x) : UnitAddCircle))
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
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hδt : Tendsto δ atTop (𝓝 0))
    {I : Set ℝ} {o' : ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    (hIo : IsOpen I)
    (hψ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hcψ₀ : HasCompactSupport ψ₀)
    (hsψ₀ : tsupport ψ₀ ⊆ Ioc o' (o'+1) ∩ I)
    (heψ : ∀ x ∈ Ioc o' (o'+1), ψ₀ x = ψ (x : UnitAddCircle))
    (hψc : Continuous ψ) (hχc : Continuous χ.uncurry) (hcχ : HasCompactSupport χ.uncurry)
    (hzχ : ∀ a, χ 0 a = 0)
    (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1) (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s ≠ 0 → χ s a = 1)
    {Q : ℕ} (hQ : 0 < Q) (h : ℤ) :
    let F := stationaryCutoffLift (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1) ψ₀
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 < L → ∀ β : ℝ,
      ∀ (J₀ : ℝ → ℝ) (J : UnitAddCircle → ℝ),
      (∀ a ∈ I, J₀ a = L*a+β) →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀ → Measurable J →
      (∀ x ∈ I, J (x : UnitAddCircle) = J₀ x) →
      ∃ S : ℕ → Finset ℤ,
        (∀ n, 0 < n → ∀ k ∈ S n, h+k*(Q:ℤ) ≠ 0) ∧
        (∀ n, 0 < n → ∀ k ∉ S n, ∀ a, χ (((h+k*(Q:ℤ):ℤ):ℝ)/n) a = 0) ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
          (∫ a, |foldCircleDensity (fun t => ∑ k ∈ S n,
            unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
              (circleDensityLift o' (retainedCircleWeight ψ χ
                (fun n j => exactPassageCoeff m (H n) A j) n (h+k*(Q:ℤ))))
              n ((h+k*(Q:ℤ):ℤ):ℝ) t) a-
            foldCircleDensity (fun s => (Q:ℝ)⁻¹*(∫ a, F (a,s))) a|
            ∂AddCircle.haarAddCircle) < C/L+η := by
  sorry

end ThreeTorus
end
end

end OAI
end
