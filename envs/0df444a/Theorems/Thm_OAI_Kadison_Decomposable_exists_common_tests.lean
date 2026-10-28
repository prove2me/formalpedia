-- Prove2me | Theorems.Thm_OAI_Kadison_Decomposable_exists_common_tests
-- name    : OAI.Kadison.Decomposable.exists_common_tests
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:42:52.214832+00:00
-- url     : https://prove2.me/theorems/9651c09c-70ff-4986-bec5-1a4aa7444be0
-- title:
--   OAI.Kadison.Decomposable.exists_common_tests: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.Decomposable`, with `open MeasureTheory Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem exists_common_tests
--       (ρ : A →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ))
--       (σ : Ω → A →⋆ₐ[ℂ] (H →L[ℂ] H))
--       (hm : ∀ a ξ,AEStronglyMeasurable (fun x => σ x a ξ) μ)
--       (hact : ∀ a (f : Lp H 2 μ),ρ a f =ᵐ[μ] fun x => σ x a (f x)) :
--       ∃ (test : ℕ → Ω → H →L[ℂ] H)
--         (ht : ∀ n ξ,AEStronglyMeasurable (fun x => test n x ξ) μ)
--         (hb : ∀ n,∀ᵐ x ∂μ,‖test n x‖≤1),
--         (∀ n,operator μ (test n) (ht n) (hb n)∈NormalGNS.bicommutant ρ.range) ∧
--         (∀ n,∀ᵐ x ∂μ,test n x∈NormalGNS.bicommutant (σ x).range) ∧
--         (∀ᵐ x ∂μ,∀ T : H →L[ℂ] H,T∈NormalGNS.bicommutant (σ x).range → ‖T‖≤1 →
--           ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => test (k n) x ξ) atTop (𝓝 (T ξ))) ∧
--         (∀ T : Lp H 2 μ →L[ℂ] Lp H 2 μ,T∈NormalGNS.bicommutant ρ.range → ‖T‖≤1 →
--           ∃ k : ℕ → ℕ,∀ f,Tendsto
--             (fun n => operator μ (test (k n)) (ht (k n)) (hb (k n)) f) atTop (𝓝 (T f)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.bicommutant` (definitions bundle `OAIQ039C011` of this split); `OAI.Kadison.Decomposable.operator` (definitions bundle `OAIQ039C022` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.Decomposable.uniform_commutator_in_central_spectral_model_nonzero` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C011
import Definitions.Def_OAIQ039C022

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology

namespace Kadison.Decomposable

variable {Ω H A : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp H 2 μ)]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [TopologicalSpace.SeparableSpace A]

omit [IsFiniteMeasure μ] in
theorem exists_common_tests
    (ρ : A →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (σ : Ω → A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hm : ∀ a ξ,AEStronglyMeasurable (fun x => σ x a ξ) μ)
    (hact : ∀ a (f : Lp H 2 μ),ρ a f =ᵐ[μ] fun x => σ x a (f x)) :
    ∃ (test : ℕ → Ω → H →L[ℂ] H)
      (ht : ∀ n ξ,AEStronglyMeasurable (fun x => test n x ξ) μ)
      (hb : ∀ n,∀ᵐ x ∂μ,‖test n x‖≤1),
      (∀ n,operator μ (test n) (ht n) (hb n)∈NormalGNS.bicommutant ρ.range) ∧
      (∀ n,∀ᵐ x ∂μ,test n x∈NormalGNS.bicommutant (σ x).range) ∧
      (∀ᵐ x ∂μ,∀ T : H →L[ℂ] H,T∈NormalGNS.bicommutant (σ x).range → ‖T‖≤1 →
        ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => test (k n) x ξ) atTop (𝓝 (T ξ))) ∧
      (∀ T : Lp H 2 μ →L[ℂ] Lp H 2 μ,T∈NormalGNS.bicommutant ρ.range → ‖T‖≤1 →
        ∃ k : ℕ → ℕ,∀ f,Tendsto
          (fun n => operator μ (test (k n)) (ht (k n)) (hb (k n)) f) atTop (𝓝 (T f))) := by
  sorry

end Kadison.Decomposable

end

end
end

end OAI
end
