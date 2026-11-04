-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_commutatorEstimate_of_centralDecomposition
-- name    : OAI.KadisonSimilarity.commutatorEstimate_of_centralDecomposition
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T09:59:35.940982+00:00
-- url     : https://prove2.me/theorems/1fe2e0ab-4b23-4e7a-ba20-90f25812ab98
-- title:
--   OAI.KadisonSimilarity.commutatorEstimate_of_centralDecomposition: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.commutatorEstimate_of_centralDecomposition` of [lean/OAI/Analysis/KadisonSimilarity/Representation/CentralDecomposition.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Representation/CentralDecomposition.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`, with `open MeasureTheory Filter ContinuousLinearMapWOT`, `open scoped Topology`):
--
--   ```lean
--   theorem commutatorEstimate_of_centralDecomposition
--       (D : CentralDecompositionData μ K P)
--       (approximation : SpectralStepApproximation (vonNeumannCenter P))
--       (cases : ∀ᵐ a ∂μ, PublishedFactorCasesInput (D.algebra a))
--       (dickson : ∀ᵐ a ∂μ, DicksonTwoBound (A := D.algebra a) (RectangularSum (K a) (K a))) :
--       CommutatorEstimate P universalConstant
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.RectangularSum` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.SpectralStepApproximation`, `OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed`, `OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass` and `OAI.KadisonSimilarity.vonNeumannCenter` (definitions bundle `OAIQ075A005` of this split); `OAI.KadisonSimilarity.DicksonTwoBound` (definitions bundle `OAIQ075A010` of this split); `OAI.vonNeumannAlgebraStarOrderedRing` (definitions bundle `OAIQ075A012` of this split); `OAI.KadisonSimilarity.CentralDecompositionData` (definitions bundle `OAIQ075A023` of this split); `OAI.KadisonSimilarity.PublishedFactorCasesInput` (definitions bundle `OAIQ075A033` of this split); `OAI.KadisonSimilarity.CommutatorEstimate` and `OAI.KadisonSimilarity.universalConstant` (the published bundle `Def_KadisonSimilarity`).
--
--   **Used by.** The proofs of `OAI.KadisonSimilarity.uniformCommutatorEstimate`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Representation/CentralDecomposition.lean (declaration OAI.KadisonSimilarity.commutatorEstimate_of_centralDecomposition)

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A033

section

attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter ContinuousLinearMapWOT
open scoped Topology

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
  (K : Ω → Type u) [∀ a, NormedAddCommGroup (K a)]
  [∀ a, InnerProductSpace ℂ (K a)] [∀ a, CompleteSpace (K a)]

variable {μ K} {P : VonNeumannAlgebra H}

variable [∀ a, TopologicalSpace.SeparableSpace (K a)]

theorem commutatorEstimate_of_centralDecomposition
    (D : CentralDecompositionData μ K P)
    (approximation : SpectralStepApproximation (vonNeumannCenter P))
    (cases : ∀ᵐ a ∂μ, PublishedFactorCasesInput (D.algebra a))
    (dickson : ∀ᵐ a ∂μ, DicksonTwoBound (A := D.algebra a) (RectangularSum (K a) (K a))) :
    CommutatorEstimate P universalConstant := by
  sorry

end KadisonSimilarity

end

end OAI
end
