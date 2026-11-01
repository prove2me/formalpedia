-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_TracialRepeatedWordRealization_propagation_on_base_of_published_inputs
-- name    : OAI.KadisonSimilarity.TracialRepeatedWordRealization.propagation_on_base_of_published_inputs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T08:52:14.664802+00:00
-- url     : https://prove2.me/theorems/4d7a05e7-e25b-4d88-b51e-a53f6f5f6c7a
-- title:
--   OAI.KadisonSimilarity.TracialRepeatedWordRealization.propagation_on_base_of_published_inputs (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.TracialRepeatedWordRealization.propagation_on_base_of_published_inputs` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialPropagationEndgame.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialPropagationEndgame.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity.TracialRepeatedWordRealization`):
--
--   ```lean
--   theorem propagation_on_base_of_published_inputs
--       (R : TracialRepeatedWordRealization W z a Y B₀ Bₖ)
--       (hτ : GD.trace 1 = 1) (ha : 0 < a)
--       (htrace : GD.trace q = (a : ℂ)) (hhaar : HaarCornerMoments GD.trace z a)
--       (τ : P → ℝ) (support : TracialRightSupportInput τ (ι q) A)
--       (hsmall : ∀ v : A, R.small (G.baseVector A v) = G.vector (ι q * (v : P)))
--       (e : P) (he : IsStarProjection e) (hqe : τ (ι q) ≤ τ e)
--       (hfaithful : Function.Injective G.vector)
--       (comparison : FiniteFactorProjectionComparison τ)
--       {n : ℕ} (hn : 0 < n) (frame : Fin n → P)
--       (hframe : ∀ i j, star (frame i) * frame j = if i = j then e else 0)
--       (hsum : ∑ i, frame i * star (frame i) = 1)
--       (hYe : Y.comp (G.left e) = (G.left e).comp Y)
--       (hYframe : ∀ i, Y.comp (G.left (frame i)) = (G.left (frame i)).comp Y)
--       {ε : ℝ} (hε : 0 ≤ ε)
--       (hY : ∀ x : CStarCorner e he, ‖commutator Y (G.left (x : P))‖ ≤ ε * ‖x‖)
--       (published : PublishedDerivationInputs.{u,v} (CStarCorner e he))
--       (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful))
--       (v : G.baseSpace A) :
--       ‖Bₖ (R.repeatVector v) - R.repeatVector (B₀ v)‖ ≤
--         2 * cyclicConstant * ε * ‖v‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.closedSubmoduleInner`, `OAI.closedSubmoduleNormedAddCommGroup`, `OAI.closedSubmoduleNormedSpace`, `OAI.KadisonSimilarity.CStarCorner`, `OAI.KadisonSimilarity.FiniteFactorProjectionComparison`, `OAI.KadisonSimilarity.HaarCornerMoments`, `OAI.KadisonSimilarity.TracialCornerGeometry`, `OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex`, `OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex`, `OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex` and `OAI.KadisonSimilarity.CStarCorner.instStarOrderedRingSubtypeMemNonUnitalStarSubalgebraComplex` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.TracialCommutationInput` and `OAI.KadisonSimilarity.TracialRightSupportInput` (definitions bundle `OAIQ075A005` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace` and `OAI.KadisonSimilarity.TracialCornerGeometry.baseVector` (definitions bundle `OAIQ075A016` of this split); `OAI.KadisonSimilarity.PublishedDerivationInputs` (definitions bundle `OAIQ075A017` of this split); `OAI.KadisonSimilarity.TracialHeadCoordinates`, `OAI.KadisonSimilarity.TracialRepeatedWordRealization`, `OAI.KadisonSimilarity.TracialCornerGeometry.faithfulRightAction` and `OAI.KadisonSimilarity.TracialHeadCoordinates.vacuum` (definitions bundle `OAIQ075A024` of this split); `OAI.KadisonSimilarity.commutator` and `OAI.KadisonSimilarity.cyclicConstant` (the published bundle `Def_KadisonSimilarity`).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialPropagationEndgame.lean (declaration OAI.KadisonSimilarity.TracialRepeatedWordRealization.propagation_on_base_of_published_inputs)

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A024

section

attribute [-instance] _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity

universe u v
variable {P : Type u} {H : Type v} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {D E F V : Type*} [CStarAlgebra D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {GD : TracialCornerGeometry D E} {G : TracialCornerGeometry P H}
  {ι : D →⋆ₐ[ℂ] P} {W : TracialHeadCoordinates GD G ι F}
  [W.vacuum.HasOrthogonalProjection]
  {q : D} {hq : IsStarProjection q} {z : unitary (CStarCorner q hq)} {a : ℝ}
  {Y : H →L[ℂ] H} {A : StarSubalgebra ℂ P}
  {B₀ : G.baseSpace A →L[ℂ] G.baseSpace A} {Bₖ : V →L[ℂ] V}

namespace TracialRepeatedWordRealization

theorem propagation_on_base_of_published_inputs
    (R : TracialRepeatedWordRealization W z a Y B₀ Bₖ)
    (hτ : GD.trace 1 = 1) (ha : 0 < a)
    (htrace : GD.trace q = (a : ℂ)) (hhaar : HaarCornerMoments GD.trace z a)
    (τ : P → ℝ) (support : TracialRightSupportInput τ (ι q) A)
    (hsmall : ∀ v : A, R.small (G.baseVector A v) = G.vector (ι q * (v : P)))
    (e : P) (he : IsStarProjection e) (hqe : τ (ι q) ≤ τ e)
    (hfaithful : Function.Injective G.vector)
    (comparison : FiniteFactorProjectionComparison τ)
    {n : ℕ} (hn : 0 < n) (frame : Fin n → P)
    (hframe : ∀ i j, star (frame i) * frame j = if i = j then e else 0)
    (hsum : ∑ i, frame i * star (frame i) = 1)
    (hYe : Y.comp (G.left e) = (G.left e).comp Y)
    (hYframe : ∀ i, Y.comp (G.left (frame i)) = (G.left (frame i)).comp Y)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hY : ∀ x : CStarCorner e he, ‖commutator Y (G.left (x : P))‖ ≤ ε * ‖x‖)
    (published : PublishedDerivationInputs.{u,v} (CStarCorner e he))
    (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful))
    (v : G.baseSpace A) :
    ‖Bₖ (R.repeatVector v) - R.repeatVector (B₀ v)‖ ≤
      2 * cyclicConstant * ε * ‖v‖ := by
  sorry

end TracialRepeatedWordRealization
end KadisonSimilarity

end

end OAI
end
