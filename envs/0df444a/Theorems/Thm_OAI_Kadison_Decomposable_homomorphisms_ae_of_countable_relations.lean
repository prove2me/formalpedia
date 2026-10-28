-- Prove2me | Theorems.Thm_OAI_Kadison_Decomposable_homomorphisms_ae_of_countable_relations
-- name    : OAI.Kadison.Decomposable.homomorphisms_ae_of_countable_relations
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:41:58.762101+00:00
-- url     : https://prove2.me/theorems/7b31f7c8-9c9b-4390-afb6-020e1dd846bc
-- title:
--   OAI.Kadison.Decomposable.homomorphisms_ae_of_countable_relations: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.Decomposable`, with `open MeasureTheory Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem homomorphisms_ae_of_countable_relations
--       (S : StarSubalgebra ℚ A) [Countable S]
--       (hd : DenseRange (fun a : S => (a:A))) (hI : Complex.I • (1:A)∈S)
--       (T : A → Ω → H →L[ℂ] H)
--       (hb : ∀ a,∀ᵐ x ∂μ,‖T a x‖≤‖a‖)
--       (ha : ∀ a b,∀ᵐ x ∂μ,T (a+b) x=T a x+T b x)
--       (hm : ∀ a b,∀ᵐ x ∂μ,T (a*b) x=T a x*T b x)
--       (hst : ∀ a,∀ᵐ x ∂μ,T (star a) x=star (T a x))
--       (hsc : ∀ z : ℂ,∀ᵐ x ∂μ,T (z • (1:A)) x=z • (1:H →L[ℂ] H)) :
--       ∀ᵐ x ∂μ,∃ Φ : A →⋆ₐ[ℂ] (H →L[ℂ] H),∀ a : S,Φ (a:A)=T (a:A) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.Decomposable.instNormedAlgebraRat_solutions` (definitions bundle `OAIQ039C007` of this split); `OAI.Kadison.Decomposable.instStarModuleRat_solutions` (definitions bundle `OAIQ039C023` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.Decomposable.exists_pointwise_starHom` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C023

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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
  [TopologicalSpace.SeparableSpace H] [IsFiniteMeasure μ] [CStarAlgebra A]

attribute [local instance] OAI.Kadison.Decomposable.instNormedAlgebraRat_solutions
attribute [local instance] OAI.Kadison.Decomposable.instNormedAlgebraRatContinuousLinearMapComplexId_solutions
attribute [local instance] OAI.Kadison.Decomposable.instStarModuleRat_solutions
local instance instStarModuleRatContinuousLinearMapComplexId_solutions_r73cf57_1 : StarModule ℚ (H →L[ℂ] H) where
  star_smul r a := by
    change star ((r:ℂ) • a)=((star r:ℚ):ℂ) • star a
    simp
omit [TopologicalSpace.SeparableSpace H] [IsFiniteMeasure μ] in
theorem homomorphisms_ae_of_countable_relations
    (S : StarSubalgebra ℚ A) [Countable S]
    (hd : DenseRange (fun a : S => (a:A))) (hI : Complex.I • (1:A)∈S)
    (T : A → Ω → H →L[ℂ] H)
    (hb : ∀ a,∀ᵐ x ∂μ,‖T a x‖≤‖a‖)
    (ha : ∀ a b,∀ᵐ x ∂μ,T (a+b) x=T a x+T b x)
    (hm : ∀ a b,∀ᵐ x ∂μ,T (a*b) x=T a x*T b x)
    (hst : ∀ a,∀ᵐ x ∂μ,T (star a) x=star (T a x))
    (hsc : ∀ z : ℂ,∀ᵐ x ∂μ,T (z • (1:A)) x=z • (1:H →L[ℂ] H)) :
    ∀ᵐ x ∂μ,∃ Φ : A →⋆ₐ[ℂ] (H →L[ℂ] H),∀ a : S,Φ (a:A)=T (a:A) x := by
  sorry

end Kadison.Decomposable

end

end
end

end OAI
end
