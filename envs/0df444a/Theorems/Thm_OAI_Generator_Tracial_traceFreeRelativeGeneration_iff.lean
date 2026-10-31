-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_traceFreeRelativeGeneration_iff
-- name    : OAI.Generator.Tracial.traceFreeRelativeGeneration_iff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T16:00:12.823885+00:00
-- url     : https://prove2.me/theorems/48e1c001-ac16-4993-8553-3a1a6f5c9a64
-- title:
--   OAI.Generator.Tracial.traceFreeRelativeGeneration_iff: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.traceFreeRelativeGeneration_iff` of [lean/OAI/Analysis/RelativeGeneration/InclusionTransport.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RelativeGeneration/InclusionTransport.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open UltrapowerBridge`):
--
--   ```lean
--   theorem traceFreeRelativeGeneration_iff (u : M.toStarSubalgebra) :
--       wstar ((P : Set (H →L[ℂ] H)) ∪ {u.val}) = M.toStarSubalgebra ↔
--         wstar ((N : Set (K →L[ℂ] K)) ∪ {π u}) = (R).toStarSubalgebra
--   ```
--
--   **Definitions.** The statement is written with `OAI.Generator.Tracial.TraceFreePreHilbert` and `OAI.Generator.Tracial.traceFreePreHilbertRing` (definitions bundle `OAIQ11Fg002` of this split); `OAI.Generator.Tracial.TraceFreeHilbert`, `OAI.Generator.Tracial.traceFreePreHilbertInnerProductSpace` and `OAI.Generator.Tracial.traceFreePreHilbertNormedAddCommGroup` (definitions bundle `OAIQ11Fg017` of this split); `OAI.Generator.Tracial.traceFreeHilbertAction` and `OAI.Generator.Tracial.traceFreeHilbertClosure` (definitions bundle `OAIQ11Fg018` of this split); `OAI.Generator.Tracial.traceFreeRelativeImage` (definitions bundle `OAIQ129Rg000` of this split); `OAI.Generator.WOTClosed` and `OAI.Generator.wstar` (the published bundle `Def_FactorGeneration`).
--
--   **Used by.** The proof of `OAI.RelativeGeneration.main_theorem` of this split imports it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RelativeGeneration/InclusionTransport.lean (declaration OAI.Generator.Tracial.traceFreeRelativeGeneration_iff)

import Mathlib
import Definitions.Def_FactorGeneration
import Definitions.Def_OAIQ129Rg000

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed

namespace OAI

noncomputable section

namespace Generator.Tracial
open UltrapowerBridge
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
local notation "R" => traceFreeHilbertClosure hfactor hdiff hfinite hunit
local notation "e" => traceFreeHilbertEquiv hfactor hdiff hfinite hunit

variable (P : StarSubalgebra ℂ (H →L[ℂ] H)) (hP : WOTClosed P)
local notation "N" => traceFreeRelativeImage hfactor hdiff hfinite hunit P hP

variable (hPM : P ≤ M.toStarSubalgebra)

include hPM in
theorem traceFreeRelativeGeneration_iff (u : M.toStarSubalgebra) :
    wstar ((P : Set (H →L[ℂ] H)) ∪ {u.val}) = M.toStarSubalgebra ↔
      wstar ((N : Set (K →L[ℂ] K)) ∪ {π u}) = (R).toStarSubalgebra := by
  sorry

end Generator.Tracial

end

end OAI
end
