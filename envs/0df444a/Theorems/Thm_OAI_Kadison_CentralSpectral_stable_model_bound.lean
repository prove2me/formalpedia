-- Prove2me | Theorems.Thm_OAI_Kadison_CentralSpectral_stable_model_bound
-- name    : OAI.Kadison.CentralSpectral.stable_model_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T07:01:33.457237+00:00
-- url     : https://prove2.me/theorems/b8f12e08-0729-474c-9c73-c27dbe5aef4d
-- title:
--   OAI.Kadison.CentralSpectral.stable_model_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.CentralSpectral`, with `open MeasureTheory Filter`, `open scoped Topology InnerProductSpace ComplexOrder`, `open CyclicSpectral Decomposable InfiniteAmplification`):
--
--   ```lean
--   lemma stable_model_bound (Y : Space ℕ H →L[ℂ] Space ℕ H)
--       (h : ℕ) (hh : 1≤h) (X : Matrix (Fin h) (Fin h) (Space ℕ H →L[ℂ] Space ℕ H))
--       (hX : ∀ i j,X i j∈algebra M) :
--       ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
--         9368*commutatorSeminorm (algebra M) Y*‖matrixOperator h X‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.CentralCorner.center` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.InfiniteAmplification.Space` and `OAI.Kadison.InfiniteAmplification.map` (definitions bundle `OAIQ039C006` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.InfiniteAmplification.algebra` (definitions bundle `OAIQ039C027` of this split); `OAI.Kadison.CyclicSpectral.scalarMultiplier` and `OAI.Kadison.Decomposable.indicatorOperator` (definitions bundle `OAIQ039C033` of this split); `OAI.Kadison.Decomposable.scalarVectorMultiplier` (definitions bundle `OAIQ039C035` of this split); `OAI.Kadison.CentralSpectral.Spectrum`, `OAI.Kadison.CentralSpectral.centerCommCStar`, `OAI.Kadison.CentralSpectral.spectrumBorel` and `OAI.Kadison.CentralSpectral.spectrumMeasurable` (definitions bundle `OAIQ039C054` of this split); `OAI.Kadison.commutatorSeminorm`, `OAI.Kadison.diagonalAmplification` and `OAI.Kadison.matrixOperator` (the published bundle `Def_UniformCommutator`).
--
--   **Used by.** The proof of `OAI.Kadison.CentralSpectral.separable_uniform_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C027
import Definitions.Def_OAIQ039C054

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open MeasureTheory Filter

open scoped Topology InnerProductSpace ComplexOrder

namespace Kadison.CentralSpectral

open CyclicSpectral Decomposable InfiniteAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (μ : Measure (Spectrum M))

variable (U : Space ℕ H ≃ₗᵢ[ℂ] Lp (Space ℕ ℂ) 2 μ)

variable (hU : ∀ (a : CentralCorner.center M) (v : Space ℕ H),
  U (map (a : H →L[ℂ] H) v)=scalarVectorMultiplier μ (gelfandStarTransform _ a) (U v))

variable (hind : ∀ (s : Set (Spectrum M)) (hs : MeasurableSet s),
  ∃ a : CentralCorner.center M,
    scalarMultiplier μ (gelfandStarTransform _ a)=indicatorOperator μ s hs)

include hU hind

variable [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace (Lp (Space ℕ ℂ) 2 μ)]

lemma stable_model_bound (Y : Space ℕ H →L[ℂ] Space ℕ H)
    (h : ℕ) (hh : 1≤h) (X : Matrix (Fin h) (Fin h) (Space ℕ H →L[ℂ] Space ℕ H))
    (hX : ∀ i j,X i j∈algebra M) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
      9368*commutatorSeminorm (algebra M) Y*‖matrixOperator h X‖ := by
  sorry

end Kadison.CentralSpectral

end

end
end

end OAI
end
