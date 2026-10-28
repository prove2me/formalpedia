-- Prove2me | Theorems.Thm_OAI_Rokhlin_local_moving_cancellation
-- name    : OAI.Rokhlin.local_moving_cancellation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:48:23.050423+00:00
-- url     : https://prove2.me/theorems/7227184e-7658-441c-b454-19dafdc112e2
-- title:
--   OAI.Rokhlin.local_moving_cancellation: intermediate lemma from OpenAI, Rokhlin's multiple-mixing problem for one transformation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Rokhlin.mixing_all_finite_orders`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rokhlin's multiple-mixing problem for one transformation*, OpenAI Math Release, September 23, 2026, result family 145, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Rokhlin.local_moving_cancellation` of [lean/OAI/Dynamics/MultipleMixing/MultipleMixing/OrbitCancellation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/OrbitCancellation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Rokhlin`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology BigOperators ComplexConjugate`):
--
--   ```lean
--   lemma local_moving_cancellation :
--       Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
--         (E.restrictLevel ψ hψ ((D.symm^[n]) b)).fibreSum
--           (absoluteCoefficient κ (f ∘ R^[n])) a) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Rokhlin.BorelFibreEnumeration`, `OAI.Rokhlin.HilbertCode`, `OAI.Rokhlin.MeasurableCircle`, `OAI.Rokhlin.ProjectiveCircle`, `OAI.Rokhlin.absoluteCoefficient`, `OAI.Rokhlin.instMeasurableSpaceHilbertCode`, `OAI.Rokhlin.localGroupBlock`, `OAI.Rokhlin.localProjectiveGroup`, `OAI.Rokhlin.phaseSubgroup`, `OAI.Rokhlin.BorelFibreEnumeration.fibreSum`, `OAI.Rokhlin.BorelFibreEnumeration.restrictLevel` and `OAI.Rokhlin.HilbertCode.projective` (definitions bundle `OAIQ3Ro000` of this split); `OAI.Rokhlin.ProjectiveCharacters` and `OAI.Rokhlin.wordEntropy` (definitions bundle `OAIQ3Ro001` of this split); `OAI.Rokhlin.projectiveCharacter` (definitions bundle `OAIQ3Ro002` of this split).
--
--   **Used by.** The proof of `OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_correlation_zero` of this split imports it.
-- source:
--   OpenAI, Rokhlin's multiple-mixing problem for one transformation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 145; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/OrbitCancellation.lean (declaration OAI.Rokhlin.local_moving_cancellation)

import Mathlib
import Definitions.Def_OAIQ3Ro002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators ComplexConjugate
variable {U Y X A C : Type*} [MeasurableSpace U] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y] [MeasurableSpace X]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace C] [MeasurableSingletonClass C]
    (κ : Kernel U Y) [IsMarkovKernel κ] (S : Set (U × HilbertCode κ))
    (E : BorelFibreEnumeration S) (ψ : U × HilbertCode κ → C) (hψ : Measurable ψ)
    (D : C ≃ C) (a₀ a : U) (b : C)
    (hb : {g : localProjectiveGroup κ S a₀ | localGroupBlock κ S ψ a₀ g = b}.Finite)
    (G : localProjectiveGroup κ S a₀ ≃* localProjectiveGroup κ S a₀)
    (hG : ∀ g, localGroupBlock κ S ψ a₀ (G g) = D.symm (localGroupBlock κ S ψ a₀ g))
    (J : localProjectiveGroup κ S a₀ ≃* localProjectiveGroup κ S a)
    (hJ : ∀ g, localGroupBlock κ S ψ a (J g) = localGroupBlock κ S ψ a₀ g)
    (e : {q // (a,q) ∈ S} ≃ localProjectiveGroup κ S a)
    (he : ∀ q, (e q).val = HilbertCode.projective a q.val)
    (hχ : ProjectiveCharacters (κ a)
      (fun g : Additive (localProjectiveGroup κ S a) => projectiveCharacter (κ a) g.toMul.val))
    {μ : Measure X} [IsProbabilityMeasure μ]
    (x : Y → X) (hx : MeasurePreserving x (κ a) μ)
    (t : ℕ → X → X) (ht : ∀ m, MeasurePreserving (t m) μ μ)
    (htadd : ∀ c d z, t (c+d) z = t d (t c z))
    (hmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun m => μ (A ∩ t m ⁻¹' B)) atTop (𝓝 (μ A * μ B)))
    (α : X → A) (hα : Measurable α) (v : A → ℂ)
    (hcenter : ∫ z, v (α z) ∂μ = 0)
    (hH : Tendsto (fun n : ℕ => wordEntropy (η := μ) (fun m z => α (t m z)) n / n)
      atTop (𝓝 0))
    (R : Y → Y) (f : Y → ℂ) (hf : ∀ n y, f ((R^[n]) y) = v (α (t n (x y))))
include hb hG hJ he hχ hx ht htadd hmix hα hcenter hH hf in
lemma local_moving_cancellation :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      (E.restrictLevel ψ hψ ((D.symm^[n]) b)).fibreSum
        (absoluteCoefficient κ (f ∘ R^[n])) a) atTop (𝓝 0) := by
  sorry
end

end Rokhlin

end

end OAI
end
