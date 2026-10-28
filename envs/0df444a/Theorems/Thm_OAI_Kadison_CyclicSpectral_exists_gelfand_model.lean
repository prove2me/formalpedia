-- Prove2me | Theorems.Thm_OAI_Kadison_CyclicSpectral_exists_gelfand_model
-- name    : OAI.Kadison.CyclicSpectral.exists_gelfand_model
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:51:07.279587+00:00
-- url     : https://prove2.me/theorems/2780c399-48d0-4d7f-87b1-826db56f0e1b
-- title:
--   OAI.Kadison.CyclicSpectral.exists_gelfand_model: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.CyclicSpectral`, with `open MeasureTheory`, `open scoped Topology`):
--
--   ```lean
--   theorem exists_gelfand_model (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
--       (hd : DenseRange (fun a : A => ρ a ξ)) :
--       ∃ μ : Measure (spectrumSpace (A:=A)), IsFiniteMeasure μ ∧
--         ∃ U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] H,
--           ∀ (a : A) (v : Lp ℂ 2 μ), U (scalarMultiplier μ (gelfandStarTransform A a) v)=ρ a (U v)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.CyclicSpectral.spectrumSpace` (definitions bundle `OAIQ039C005` of this split); `OAI.Kadison.CyclicSpectral.scalarMultiplier` (definitions bundle `OAIQ039C033` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.CentralSpectral.exists_stable_center_spectral_model` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C033

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory

open scoped Topology

namespace Kadison.CyclicSpectral

variable {A H : Type*} [CommCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [MeasurableSpace (spectrumSpace (A:=A))] [BorelSpace (spectrumSpace (A:=A))]

theorem exists_gelfand_model (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hd : DenseRange (fun a : A => ρ a ξ)) :
    ∃ μ : Measure (spectrumSpace (A:=A)), IsFiniteMeasure μ ∧
      ∃ U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] H,
        ∀ (a : A) (v : Lp ℂ 2 μ), U (scalarMultiplier μ (gelfandStarTransform A a) v)=ρ a (U v) := by
  sorry

end Kadison.CyclicSpectral

end

end
end

end OAI
end
