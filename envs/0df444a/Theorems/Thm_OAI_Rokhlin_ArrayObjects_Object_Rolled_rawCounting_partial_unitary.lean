-- Prove2me | Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_rawCounting_partial_unitary
-- name    : OAI.Rokhlin.ArrayObjects.Object.Rolled.rawCounting_partial_unitary
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-26T06:43:57.715993+00:00
-- url     : https://prove2.me/theorems/8c1e1c8c-64cb-4d7a-ab7d-6f5dd9767e94
-- title:
--   OAI.Rokhlin.ArrayObjects.Object.Rolled.rawCounting_partial_unitary: intermediate lemma from OpenAI, Rokhlin's multiple-mixing problem for one transformation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Rokhlin.mixing_all_finite_orders`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rokhlin's multiple-mixing problem for one transformation*, OpenAI Math Release, September 23, 2026, result family 145, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Rokhlin.ArrayObjects.Object.Rolled.rawCounting_partial_unitary` of [lean/OAI/Dynamics/MultipleMixing/MultipleMixing/FibreMeasures.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/FibreMeasures.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Rokhlin.ArrayObjects.Object.Rolled`, with `open MeasureTheory ProbabilityTheory Set ContinuousLinearMap`):
--
--   ```lean
--   lemma rawCounting_partial_unitary :
--       let hq := rawCounting_coordinate_preserving M Λ hk hm hind S hS E Eπ
--       let A := JoiningOperator.operator (hq s) (hq t)
--       A = A.adjoint * A * A ∧ A = A * A * A.adjoint
--   ```
--
--   **Definitions.** The statement is written with `OAI.Rokhlin.BorelFibreEnumeration`, `OAI.Rokhlin.HilbertCode`, `OAI.Rokhlin.exactCodeSet`, `OAI.Rokhlin.instMeasurableSpaceHilbertCode`, `OAI.Rokhlin.ArrayObjects.Arr`, `OAI.Rokhlin.ArrayObjects.Index`, `OAI.Rokhlin.ArrayObjects.InitialLaws`, `OAI.Rokhlin.ArrayObjects.Object`, `OAI.Rokhlin.ArrayObjects.StandardSpace`, `OAI.Rokhlin.ArrayObjects.instMeasurableSpaceα`, `OAI.Rokhlin.ArrayObjects.instStandardBorelSpaceα`, `OAI.Rokhlin.BorelFibreEnumeration.measure`, `OAI.Rokhlin.JoiningOperator.operator`, `OAI.Rokhlin.ArrayObjects.Object.IsSaturated`, `OAI.Rokhlin.ArrayObjects.Object.ownKernel`, `OAI.Rokhlin.ArrayObjects.Object.ownKernel_markov`, `OAI.Rokhlin.ArrayObjects.Object.parameterLaw`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.RawLabel`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.rawCounting_coordinate_preserving`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.rawExactSquare`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.rawLineGraph`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.rawTupleKernel` and `OAI.Rokhlin.ArrayObjects.Object.Rolled.tupleParameter` (definitions bundle `OAIQ3Ro000` of this split).
--
--   **Used by.** The proof of `OAI.Rokhlin.ArrayObjects.Object.Rolled.exists_raw_finite_levels` of this split imports it.
-- source:
--   OpenAI, Rokhlin's multiple-mixing problem for one transformation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 145; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/FibreMeasures.lean (declaration OAI.Rokhlin.ArrayObjects.Object.Rolled.rawCounting_partial_unitary)

import Mathlib
import Definitions.Def_OAIQ3Ro000

section

attribute [-instance] _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.arrayLaw_probability _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.localLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory ProbabilityTheory Set ContinuousLinearMap
namespace ArrayObjects.Object.Rolled
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

include hM hL Eσ hst in
lemma rawCounting_partial_unitary :
    let hq := rawCounting_coordinate_preserving M Λ hk hm hind S hS E Eπ
    let A := JoiningOperator.operator (hq s) (hq t)
    A = A.adjoint * A * A ∧ A = A * A * A.adjoint := by
  sorry

end ArrayObjects.Object.Rolled
end

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

end Rokhlin

end

end OAI
end
