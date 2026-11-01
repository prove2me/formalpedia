-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_canonical_free_corner_bound
-- name    : OAI.KadisonSimilarity.canonical_free_corner_bound
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T09:12:47.885383+00:00
-- url     : https://prove2.me/theorems/c8d116dc-4a34-4abb-a9ba-b7ab42d6b449
-- title:
--   OAI.KadisonSimilarity.canonical_free_corner_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.canonical_free_corner_bound` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/CanonicalFreeCornerCore.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/CanonicalFreeCornerCore.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`, with `open TracialCornerGeometry`, `open scoped ComplexOrder`):
--
--   ```lean
--   theorem canonical_free_corner_bound
--       (hf : ScalarFree τ.toLinearMap φ.range ψ.range)
--       (S : RealTracialSequence τR.toLinearMap)
--       (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
--       {b : ℝ} (Q : SmallFreeCornerData ((G).baseGeometry D₀).trace b)
--       (x : A) (hxstar : star x = x) (hxsq : x * x = 1) (hx0 : τ (φ x) = 0)
--       (published : CanonicalFreeCornerCoreInput τ htr φ ψ τR hψτ M hfτ Q x hxsq)
--       (baseExpectation : Nonempty (TracialExpectation (G).trace A₀))
--       (hnormal : ∃ N : VonNeumannAlgebra (canonicalGeneratedTrace τ htr φ ψ).GNS,
--         (G).left.range = N.toStarSubalgebra)
--       (T : τ.GNS →L[ℂ] τ.GNS)
--       (hcomm : ∀ r, T.comp (τ.gnsStarAlgHom (ψ r)) =
--         (τ.gnsStarAlgHom (ψ r)).comp T)
--       {ε : ℝ} (hε : 0 ≤ ε)
--       (hcorner : (gnsTracialGeometry τ htr).TraceCornerBound ψ.range T Q.trace ε) :
--       ‖(G).baseOperator A₀
--         (commutator (canonicalGeneratedOperator τ htr φ ψ T)
--           ((G).left (canonicalGeneratedFirst τ htr φ ψ x)))‖ ≤ cornerConstant * ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing` (definitions bundle `OAIQ075A002` of this split); `OAI.closedSubmoduleInner`, `OAI.closedSubmoduleNormedAddCommGroup`, `OAI.closedSubmoduleNormedSpace`, `OAI.KadisonSimilarity.NestedTracialMatrices`, `OAI.KadisonSimilarity.ScalarFree`, `OAI.KadisonSimilarity.TracialExpectation`, `OAI.KadisonSimilarity.gnsTracialVector` and `OAI.KadisonSimilarity.TracialCornerGeometry` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.RealTracialSequence` (definitions bundle `OAIQ075A005` of this split); `OAI.KadisonSimilarity.SmallFreeCornerData`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseOperator` and `OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace` (definitions bundle `OAIQ075A016` of this split); `OAI.KadisonSimilarity.CanonicalFreeCornerCoreInput`, `OAI.KadisonSimilarity.canonicalGeneratedAlgebra`, `OAI.KadisonSimilarity.canonicalGeneratedAlgebra_isClosed`, `OAI.KadisonSimilarity.canonicalGeneratedFirst`, `OAI.KadisonSimilarity.canonicalGeneratedGeometry`, `OAI.KadisonSimilarity.canonicalGeneratedSecond`, `OAI.KadisonSimilarity.canonicalGeneratedTrace` and `OAI.KadisonSimilarity.gnsTracialGeometry` (definitions bundle `OAIQ075A023` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.TraceCornerBound` (definitions bundle `OAIQ075A028` of this split); `OAI.KadisonSimilarity.canonicalGeneratedOperator` (definitions bundle `OAIQ075A029` of this split); `OAI.KadisonSimilarity.commutator` and `OAI.KadisonSimilarity.cornerConstant` (the published bundle `Def_KadisonSimilarity`).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.original_symmetry_bound_of_free_corner` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/CanonicalFreeCornerCore.lean (declaration OAI.KadisonSimilarity.canonical_free_corner_bound)

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A028
import Definitions.Def_OAIQ075A029

section

attribute [-instance] _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity
open TracialCornerGeometry
open scoped ComplexOrder

variable {A R P : Type*} [CStarAlgebra A] [CStarAlgebra R] [CStarAlgebra P]
  [PartialOrder R] [StarOrderedRing R] [PartialOrder P] [StarOrderedRing P]
  (τ : P →ₚ[ℂ] ℂ) (htr : ∀ a b : P, τ (a * b) = τ (b * a))
  (φ : A →⋆ₐ[ℂ] P) (ψ : R →⋆ₐ[ℂ] P)
  (hφ : Function.Injective φ) (hψ : Function.Injective ψ)

local notation "L" => canonicalGeneratedAlgebra τ htr φ ψ
local notation "G" => canonicalGeneratedGeometry τ htr φ ψ
local notation "A₀" => StarAlgHom.range (canonicalGeneratedFirst τ htr φ ψ)
local notation "D₀" => StarAlgHom.range (canonicalGeneratedSecond τ htr φ ψ)

variable [IsClosed ((canonicalGeneratedFirst τ htr φ ψ).range :
    Set (canonicalGeneratedAlgebra τ htr φ ψ))]
  [IsClosed ((canonicalGeneratedSecond τ htr φ ψ).range :
    Set (canonicalGeneratedAlgebra τ htr φ ψ))]

variable (τR : R →ₚ[ℂ] ℂ) (hψτ : ∀ r, τ (ψ r) = τR r)

variable {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) τR.toLinearMap (gnsTracialVector τR))
  (h1 : τ 1 = 1) (hfτ : ∀ a : P, τ (star a * a) = 0 → a = 0)

local notation "M₀" => canonicalGeneratedMatrices τ htr φ ψ τR hψτ M

include h1 in
theorem canonical_free_corner_bound
    (hf : ScalarFree τ.toLinearMap φ.range ψ.range)
    (S : RealTracialSequence τR.toLinearMap)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    {b : ℝ} (Q : SmallFreeCornerData ((G).baseGeometry D₀).trace b)
    (x : A) (hxstar : star x = x) (hxsq : x * x = 1) (hx0 : τ (φ x) = 0)
    (published : CanonicalFreeCornerCoreInput τ htr φ ψ τR hψτ M hfτ Q x hxsq)
    (baseExpectation : Nonempty (TracialExpectation (G).trace A₀))
    (hnormal : ∃ N : VonNeumannAlgebra (canonicalGeneratedTrace τ htr φ ψ).GNS,
      (G).left.range = N.toStarSubalgebra)
    (T : τ.GNS →L[ℂ] τ.GNS)
    (hcomm : ∀ r, T.comp (τ.gnsStarAlgHom (ψ r)) =
      (τ.gnsStarAlgHom (ψ r)).comp T)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcorner : (gnsTracialGeometry τ htr).TraceCornerBound ψ.range T Q.trace ε) :
    ‖(G).baseOperator A₀
      (commutator (canonicalGeneratedOperator τ htr φ ψ T)
        ((G).left (canonicalGeneratedFirst τ htr φ ψ x)))‖ ≤ cornerConstant * ε := by
  sorry

end KadisonSimilarity

end

end OAI
end
