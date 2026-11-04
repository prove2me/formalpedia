-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_free_corner_from_local_published_inputs
-- name    : OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_from_local_published_inputs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T09:03:50.865723+00:00
-- url     : https://prove2.me/theorems/42e2f573-6915-4b0a-9959-33980d94bce0
-- title:
--   OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_from_local_published_inputs (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_from_local_published_inputs` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/LocalFreeCornerInputs.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/LocalFreeCornerInputs.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity.TracialCornerGeometry`):
--
--   ```lean
--   theorem free_corner_from_local_published_inputs
--       (published : G.LocalFreeCornerPublishedInputs)
--       (baseExpectation : Nonempty (TracialExpectation G.trace A))
--       (hnormal : ∃ N : VonNeumannAlgebra H, G.left.range = N.toStarSubalgebra)
--       (hgen : G.FactorsTraciallyGenerate A D)
--       (S : RealTracialSequence (G.baseGeometry D).trace)
--       (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
--       (hf : ScalarFree G.trace D A)
--       (hsstar : star s = s) (hs0 : G.trace (s : P) = 0)
--       (T : H →L[ℂ] H)
--       (hTD : ∀ x : D, T.comp (G.left (x : P)) = (G.left (x : P)).comp T)
--       {ε : ℝ} (hε : 0 ≤ ε) (hcorner : G.TraceCornerBound D T Q.trace ε) :
--       ‖G.baseOperator A (commutator T (G.left (s : P)))‖ ≤
--         6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant) * ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.closedSubmoduleInner`, `OAI.closedSubmoduleNormedAddCommGroup`, `OAI.closedSubmoduleNormedSpace`, `OAI.KadisonSimilarity.NestedTracialMatrices`, `OAI.KadisonSimilarity.ScalarFree`, `OAI.KadisonSimilarity.TracialCornerGeometry` and `OAI.KadisonSimilarity.TracialExpectation` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.RealTracialSequence` (definitions bundle `OAIQ075A005` of this split); `OAI.KadisonSimilarity.SmallFreeCornerData`, `OAI.KadisonSimilarity.TracialCornerGeometry.FactorsTraciallyGenerate`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseOperator` and `OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace` (definitions bundle `OAIQ075A016` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.LocalFreeCornerPublishedInputs` (definitions bundle `OAIQ075A023` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.TraceCornerBound` (definitions bundle `OAIQ075A028` of this split); `OAI.KadisonSimilarity.commutator` and `OAI.KadisonSimilarity.cyclicConstant` (the published bundle `Def_KadisonSimilarity`).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.canonical_free_corner_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/LocalFreeCornerInputs.lean (declaration OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_from_local_published_inputs)

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A028

section

attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

universe u v

variable {P : Type u} [CStarAlgebra P]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)
  {b : ℝ} (Q : SmallFreeCornerData (G.baseGeometry D).trace b)
  (s : A) (hssq : s * s = 1)
  (hτ : G.trace 1 = 1) (hfaithful : Function.Injective G.vector)

include M hτ hssq hfaithful in
theorem free_corner_from_local_published_inputs
    (published : G.LocalFreeCornerPublishedInputs)
    (baseExpectation : Nonempty (TracialExpectation G.trace A))
    (hnormal : ∃ N : VonNeumannAlgebra H, G.left.range = N.toStarSubalgebra)
    (hgen : G.FactorsTraciallyGenerate A D)
    (S : RealTracialSequence (G.baseGeometry D).trace)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    (hf : ScalarFree G.trace D A)
    (hsstar : star s = s) (hs0 : G.trace (s : P) = 0)
    (T : H →L[ℂ] H)
    (hTD : ∀ x : D, T.comp (G.left (x : P)) = (G.left (x : P)).comp T)
    {ε : ℝ} (hε : 0 ≤ ε) (hcorner : G.TraceCornerBound D T Q.trace ε) :
    ‖G.baseOperator A (commutator T (G.left (s : P)))‖ ≤
      6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant) * ε := by
  sorry

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end
