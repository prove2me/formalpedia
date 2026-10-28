-- Prove2me | Theorems.Thm_OAI_Kadison_CyclicSpectral_stableUnitary_intertwines
-- name    : OAI.Kadison.CyclicSpectral.stableUnitary_intertwines
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:50:52.715738+00:00
-- url     : https://prove2.me/theorems/1d96c31f-c28d-4d53-b1e4-421666b9e7d6
-- title:
--   OAI.Kadison.CyclicSpectral.stableUnitary_intertwines: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.CyclicSpectral`, with `open MeasureTheory`, `open scoped Topology InnerProductSpace`, `open InfiniteAmplification Decomposable`):
--
--   ```lean
--   lemma stableUnitary_intertwines (W : Space ℕ H ≃ₗᵢ[ℂ] Space ℕ G) (V : Lp ℂ 2 μ ≃ₗᵢ[ℂ] G)
--       (S : H →L[ℂ] H) (T : G →L[ℂ] G) (f : C(Ω,ℂ))
--       (hW : ∀ x,W (map S x)=map T (W x))
--       (hV : ∀ x,V (scalarMultiplier μ f x)=T (V x)) (v : Space ℕ H) :
--       stableUnitary μ W V (map S v)=scalarVectorMultiplier μ f (stableUnitary μ W V v)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.CyclicSpectral.stableUnitary`, `OAI.Kadison.InfiniteAmplification.Space` and `OAI.Kadison.InfiniteAmplification.map` (definitions bundle `OAIQ039C006` of this split); `OAI.Kadison.CyclicSpectral.scalarMultiplier` (definitions bundle `OAIQ039C033` of this split); `OAI.Kadison.Decomposable.scalarVectorMultiplier` (definitions bundle `OAIQ039C035` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.CentralSpectral.exists_stable_center_spectral_model` of this split imports it.
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

open MeasureTheory

open scoped Topology InnerProductSpace

namespace Kadison.CyclicSpectral

open InfiniteAmplification Decomposable

variable {Ω H G : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [CompactSpace Ω]
  [BorelSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

lemma stableUnitary_intertwines (W : Space ℕ H ≃ₗᵢ[ℂ] Space ℕ G) (V : Lp ℂ 2 μ ≃ₗᵢ[ℂ] G)
    (S : H →L[ℂ] H) (T : G →L[ℂ] G) (f : C(Ω,ℂ))
    (hW : ∀ x,W (map S x)=map T (W x))
    (hV : ∀ x,V (scalarMultiplier μ f x)=T (V x)) (v : Space ℕ H) :
    stableUnitary μ W V (map S v)=scalarVectorMultiplier μ f (stableUnitary μ W V v) := by
  sorry

end Kadison.CyclicSpectral

end

end
end

end OAI
end
