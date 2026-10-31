-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_traceFreeHilbert_singlyGenerated_pullback
-- name    : OAI.Generator.Tracial.traceFreeHilbert_singlyGenerated_pullback
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T11:09:01.362633+00:00
-- url     : https://prove2.me/theorems/ece55bca-6bf1-4ad5-884c-819e78aa37b0
-- title:
--   OAI.Generator.Tracial.traceFreeHilbert_singlyGenerated_pullback: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.traceFreeHilbert_singlyGenerated_pullback` of [lean/OAI/Analysis/FactorGeneration/TraceTransport.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/TraceTransport.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open Filter`, `open scoped ComplexConjugate ComplexStarModule CStarAlgebra Pointwise Topology`, `open Filter`, `open scoped Topology CStarAlgebra`, `open Filter`, `open scoped Topology CStarAlgebra ComplexStarModule`):
--
--   ```lean
--   theorem traceFreeHilbert_singlyGenerated_pullback
--       (hgen : SinglyGenerated (N).toStarSubalgebra) : SinglyGenerated M.toStarSubalgebra
--   ```
--
--   **Definitions.** The statement is written with `OAI.Generator.Tracial.TraceFreePreHilbert` (definitions bundle `OAIQ11Fg002` of this split); `OAI.Generator.Tracial.TraceFreeHilbert`, `OAI.Generator.Tracial.traceFreePreHilbertInnerProductSpace` and `OAI.Generator.Tracial.traceFreePreHilbertNormedAddCommGroup` (definitions bundle `OAIQ11Fg017` of this split); `OAI.Generator.Tracial.traceFreeHilbertClosure` (definitions bundle `OAIQ11Fg018` of this split); `OAI.Generator.SinglyGenerated` (the published bundle `Def_FactorGeneration`).
--
--   **Used by.** The proof of `OAI.Generator.single_generation_of_II1_separable_predual` of this split imports it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/TraceTransport.lean (declaration OAI.Generator.Tracial.traceFreeHilbert_singlyGenerated_pullback)

import Mathlib
import Definitions.Def_FactorGeneration
import Definitions.Def_OAIQ11Fg018

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed

namespace OAI

noncomputable section

namespace Generator

open Filter
open scoped ComplexConjugate ComplexStarModule CStarAlgebra Pointwise Topology

open Filter
open scoped Topology CStarAlgebra

open Filter
open scoped Topology CStarAlgebra ComplexStarModule
namespace Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit

local instance traceGenerationTransportOperatorCStar_r8715ef_1 : CStarAlgebra (K →L[ℂ] K) := {}
attribute [local instance] OAI.Generator.Tracial.traceGenerationTransportCStar
local instance traceGenerationTransportOrder_r8715ef_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceGenerationTransportStarOrder_r8715ef_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
local instance traceGenerationTransportClosureCStar_r8715ef_1 : CStarAlgebra (N).toStarSubalgebra := {}
theorem traceFreeHilbert_singlyGenerated_pullback
    (hgen : SinglyGenerated (N).toStarSubalgebra) : SinglyGenerated M.toStarSubalgebra := by
  sorry

end Tracial

end Generator

end

end OAI
end
