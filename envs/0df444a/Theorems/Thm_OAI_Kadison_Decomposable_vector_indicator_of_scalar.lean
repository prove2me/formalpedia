-- Prove2me | Theorems.Thm_OAI_Kadison_Decomposable_vector_indicator_of_scalar
-- name    : OAI.Kadison.Decomposable.vector_indicator_of_scalar
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:52:53.042029+00:00
-- url     : https://prove2.me/theorems/349e3649-dfe8-4fe2-860c-ea0f95a25f91
-- title:
--   OAI.Kadison.Decomposable.vector_indicator_of_scalar: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.Decomposable`, with `open MeasureTheory Filter`, `open scoped Topology InnerProductSpace`, `open InfiniteAmplification`):
--
--   ```lean
--   lemma vector_indicator_of_scalar (f : C(Ω,ℂ)) (s : Set Ω) (hs : MeasurableSet s)
--       (hf : CyclicSpectral.scalarMultiplier μ f=indicatorOperator μ s hs) :
--       scalarVectorMultiplier (H:=Space ι ℂ) μ f=indicatorOperator μ s hs
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.InfiniteAmplification.Space` (definitions bundle `OAIQ039C006` of this split); `OAI.Kadison.CyclicSpectral.scalarMultiplier` and `OAI.Kadison.Decomposable.indicatorOperator` (definitions bundle `OAIQ039C033` of this split); `OAI.Kadison.Decomposable.scalarVectorMultiplier` (definitions bundle `OAIQ039C035` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.CentralSpectral.central_indicators` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C033
import Definitions.Def_OAIQ039C035

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

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

open InfiniteAmplification

variable {Ω H ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [Countable ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [TopologicalSpace Ω] [T2Space Ω] [CompactSpace Ω] [BorelSpace Ω]

omit [T2Space Ω] in
lemma vector_indicator_of_scalar (f : C(Ω,ℂ)) (s : Set Ω) (hs : MeasurableSet s)
    (hf : CyclicSpectral.scalarMultiplier μ f=indicatorOperator μ s hs) :
    scalarVectorMultiplier (H:=Space ι ℂ) μ f=indicatorOperator μ s hs := by
  sorry

end Kadison.Decomposable

end

end
end

end OAI
end
