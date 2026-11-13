-- Prove2me | Theorems.Thm_OAI_KadisonKastler_exists_finite_polar_coefficients
-- name    : OAI.KadisonKastler.exists_finite_polar_coefficients
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:46:54.909321+00:00
-- url     : https://prove2.me/theorems/90fbfa15-e8f4-43f4-8b37-af3e72b84f4b
-- title:
--   OAI.KadisonKastler.exists_finite_polar_coefficients: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.exists_finite_polar_coefficients` of [lean/OAI/Analysis/KadisonKastler/FiniteOperatorDuality.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/FiniteOperatorDuality.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`, with `open InnerProductSpace`, `open scoped BigOperators`):
--
--   ```lean
--   theorem exists_finite_polar_coefficients (T : E →L[ℂ] E) :
--       ∃ (n : ℕ) (x y : Fin n → E),
--         operatorTracePairing T = finiteOperatorCoefficient x y ∧
--         (∑ i, ‖x i‖ ^ 2) ≤ ‖operatorTracePairing T‖ ∧
--         (∑ i, ‖y i‖ ^ 2) ≤ ‖operatorTracePairing T‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonKastler.finiteOperatorCoefficient` and `OAI.KadisonKastler.operatorTracePairing` (definitions bundle `Q260K007` of this split).
--
--   **Used by.** The proof of `OAI.KadisonKastler.exists_near_algebra_of_finite_orbit_bound` of this split imports it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/FiniteOperatorDuality.lean (declaration OAI.KadisonKastler.exists_finite_polar_coefficients)

import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Normed.Operator.Extend
import Definitions.Def_Q260K007

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

namespace KadisonKastler

open InnerProductSpace
open scoped BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable [FiniteDimensional ℂ E]

theorem exists_finite_polar_coefficients (T : E →L[ℂ] E) :
    ∃ (n : ℕ) (x y : Fin n → E),
      operatorTracePairing T = finiteOperatorCoefficient x y ∧
      (∑ i, ‖x i‖ ^ 2) ≤ ‖operatorTracePairing T‖ ∧
      (∑ i, ‖y i‖ ^ 2) ≤ ‖operatorTracePairing T‖ := by
  sorry

end

end KadisonKastler

end OAI
end
