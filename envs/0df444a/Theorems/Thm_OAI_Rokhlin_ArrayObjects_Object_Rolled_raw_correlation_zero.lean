-- Prove2me | Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_raw_correlation_zero
-- name    : OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_correlation_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:44:40.401267+00:00
-- url     : https://prove2.me/theorems/2cdae3e4-d3da-46b1-b62f-6e7b844915d5
-- title:
--   OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_correlation_zero: intermediate lemma from OpenAI, Rokhlin's multiple-mixing problem for one transformation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Rokhlin.mixing_all_finite_orders`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rokhlin's multiple-mixing problem for one transformation*, OpenAI Math Release, September 23, 2026, result family 145, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_correlation_zero` of [lean/OAI/Dynamics/MultipleMixing/MultipleMixing/OrbitCancellation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/OrbitCancellation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Rokhlin.ArrayObjects.Object.Rolled`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology BigOperators`):
--
--   ```lean
--   lemma raw_correlation_zero (i : I) (f : I → Arr I M.Y 0 → ℂ)
--       (hf : ∀ j, Measurable (f j)) (hb : ∀ j y, ‖f j y‖ ≤ 1)
--       (hi : ∀ y, f i y = v (α (M.x (zeroEquiv I M.Y y)))) :
--       (∫ y, ∏ j, f j (plane 0 0 j y) ∂M.law 1) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Rokhlin.BorelFibreEnumeration`, `OAI.Rokhlin.HilbertCode`, `OAI.Rokhlin.exactCodeSet`, `OAI.Rokhlin.instMeasurableSpaceHilbertCode`, `OAI.Rokhlin.ArrayObjects.Arr`, `OAI.Rokhlin.ArrayObjects.Index`, `OAI.Rokhlin.ArrayObjects.InitialLaws`, `OAI.Rokhlin.ArrayObjects.Object`, `OAI.Rokhlin.ArrayObjects.StandardSpace`, `OAI.Rokhlin.ArrayObjects.instMeasurableSpaceα`, `OAI.Rokhlin.ArrayObjects.instStandardBorelSpaceα`, `OAI.Rokhlin.ArrayObjects.plane`, `OAI.Rokhlin.ArrayObjects.zeroEquiv`, `OAI.Rokhlin.ArrayObjects.Object.IsSaturated`, `OAI.Rokhlin.ArrayObjects.Object.localLaw`, `OAI.Rokhlin.ArrayObjects.Object.ownKernel`, `OAI.Rokhlin.ArrayObjects.Object.ownKernel_markov`, `OAI.Rokhlin.ArrayObjects.Object.parameterLaw`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.RawLabel`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.rawExactSquare`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.rawLineGraph`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.rawTupleKernel` and `OAI.Rokhlin.ArrayObjects.Object.Rolled.tupleParameter` (definitions bundle `OAIQ3Ro000` of this split); `OAI.Rokhlin.wordEntropy` (definitions bundle `OAIQ3Ro001` of this split).
--
--   **Used by.** The proof of `OAI.Rokhlin.ArrayObjects.Object.Rolled.saturated_correlation_zero` of this split imports it.
-- source:
--   OpenAI, Rokhlin's multiple-mixing problem for one transformation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 145; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/OrbitCancellation.lean (declaration OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_correlation_zero)

import Mathlib
import Definitions.Def_OAIQ3Ro000
import Definitions.Def_OAIQ3Ro001

section

attribute [-instance] _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.arrayLaw_probability _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.localLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

section RawCorrelation
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (E : BorelFibreEnumeration S)
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)))
    (Eσ : BorelFibreEnumeration (rawExactSquare M Λ)) (s t : I) (hst : s ≠ t)
    {μ : Measure X} [IsProbabilityMeasure μ] (hμ : M.localLaw.map M.x = μ)
    (hT : MeasurePreserving T μ μ)
    (hmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun n => μ (A ∩ (T^[n]) ⁻¹' B)) atTop (𝓝 (μ A * μ B)))
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (α : X → A) (hα : Measurable α) (v : A → ℂ)
    (hcenter : ∫ z, v (α z) ∂μ = 0)
    (hH : Tendsto (fun n : ℕ => wordEntropy (η := μ) (fun m z => α ((T^[m]) z)) n / n)
      atTop (𝓝 0))
include hM hk hL hm hind hS E Eπ Eσ hst hμ hT hmix hα hcenter hH in
lemma raw_correlation_zero (i : I) (f : I → Arr I M.Y 0 → ℂ)
    (hf : ∀ j, Measurable (f j)) (hb : ∀ j y, ‖f j y‖ ≤ 1)
    (hi : ∀ y, f i y = v (α (M.x (zeroEquiv I M.Y y)))) :
    (∫ y, ∏ j, f j (plane 0 0 j y) ∂M.law 1) = 0 := by
  sorry
end RawCorrelation
universe u
end ArrayObjects.Object.Rolled

end Rokhlin

end

end OAI
end
