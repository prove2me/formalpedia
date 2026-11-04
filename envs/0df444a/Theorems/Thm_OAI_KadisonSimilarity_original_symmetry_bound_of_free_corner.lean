-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_original_symmetry_bound_of_free_corner
-- name    : OAI.KadisonSimilarity.original_symmetry_bound_of_free_corner
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T08:53:42.418344+00:00
-- url     : https://prove2.me/theorems/c51215e3-679f-4e07-a436-89e90f76be59
-- title:
--   OAI.KadisonSimilarity.original_symmetry_bound_of_free_corner: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.original_symmetry_bound_of_free_corner` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/CanonicalFreeCornerEstimate.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/CanonicalFreeCornerEstimate.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`, with `open HochschildUltrapower`, `open TracialCornerGeometry`, `open scoped ComplexOrder`):
--
--   ```lean
--   theorem original_symmetry_bound_of_free_corner
--       (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
--       (hD : ψ.range ≤ (Φ).range)
--       (hf : ScalarFree (quotientTrace τB hB ω trB).toLinearMap
--         (constant τB hB ω trB).range ψ.range)
--       (S : RealTracialSequence τR.toLinearMap)
--       (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
--       {b : ℝ} (Q : CanonicalSecondFrame τB hB ω trB ψ hψ b)
--       (x : B) (hxstar : star x = x) (hxsq : x * x = 1) (hx0 : τB x = 0)
--       (source_balls : ∀ C : ℝ, IsClosed (gnsTracialVector τB '' Metric.closedBall (0 : B) C))
--       (published : CanonicalFreeCornerInput τB τR hB ω trB ψ hψτ hψ M Q x hxsq)
--       (rounding : SpectralProjectionRoundingInput τA)
--       (T : τB.GNS →L[ℂ] τB.GNS)
--       (hcomm : ∀ a, T.comp (τB.gnsStarAlgHom (φ a)) =
--         (τB.gnsStarAlgHom (φ a)).comp T)
--       {ε : ℝ} (hε : 0 ≤ ε)
--       (hcorner : ∀ (q : A) (hq : IsStarProjection q), (τA q).re ≤ b →
--         ∀ z : CStarCorner (φ q) (hq.map φ),
--           ‖commutator T (τB.gnsStarAlgHom (z : B))‖ ≤ ε * ‖z‖) :
--       ‖commutator T (τB.gnsStarAlgHom x)‖ ≤ cornerConstant * ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.HochschildCStarQuotient.quotientStar`, `OAI.HochschildCStarQuotient.quotientStarModule`, `OAI.HochschildCStarQuotient.quotientStarRing`, `OAI.KadisonSimilarity.CStarCorner`, `OAI.KadisonSimilarity.NestedTracialMatrices`, `OAI.KadisonSimilarity.ScalarFree`, `OAI.KadisonSimilarity.gnsTracialVector` and `OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.RealTracialSequence` and `OAI.KadisonSimilarity.SpectralProjectionRoundingInput` (definitions bundle `OAIQ075A005` of this split); `OAI.HochschildUltrapower.Ultrapower`, `OAI.HochschildUltrapower.constant`, `OAI.HochschildUltrapower.ideal`, `OAI.HochschildUltrapower.ideal_starClosed`, `OAI.HochschildUltrapower.ideal_twoSided`, `OAI.HochschildUltrapower.quotientTrace` and `OAI.HochschildUltrapower.ultrapowerOrder` (definitions bundle `OAIQ075A009` of this split); `OAI.KadisonSimilarity.CanonicalFreeCornerInput`, `OAI.KadisonSimilarity.CanonicalSecondFrame` and `OAI.KadisonSimilarity.tracialUltrapowerMap` (definitions bundle `OAIQ075A023` of this split); `OAI.KadisonSimilarity.commutator` and `OAI.KadisonSimilarity.cornerConstant` (the published bundle `Def_KadisonSimilarity`).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.finite_standard_bound_of_local_free_corner` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/CanonicalFreeCornerEstimate.lean (declaration OAI.KadisonSimilarity.original_symmetry_bound_of_free_corner)

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A023

section

attribute [-instance] _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open TracialCornerGeometry
open scoped ComplexOrder

variable {A B R : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra R]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder R] [StarOrderedRing R]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ) (τR : R →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b : A, τA (a * b) = τA (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)

local notation "τQ" => quotientTrace τB hB ω trB
local notation "trQ" => quotientTrace_tracial τB hB ω trB
local notation "ι" => constant τB hB ω trB
local notation "Φ" => tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ

variable (ψ : R →⋆ₐ[ℂ] Ultrapower τB hB ω trB)
  (hψτ : ∀ r, quotientTrace τB hB ω trB (ψ r) = τR r)
  (hfB : ∀ a : B, τB (star a * a) = 0 → a = 0)
  (hψ : Function.Injective ψ)

local notation "L" => canonicalGeneratedAlgebra τQ trQ ι ψ
local notation "D₀" => StarAlgHom.range (canonicalGeneratedSecond τQ trQ ι ψ)

variable {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) τR.toLinearMap (gnsTracialVector τR))

include hfB in
theorem original_symmetry_bound_of_free_corner
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (hD : ψ.range ≤ (Φ).range)
    (hf : ScalarFree (quotientTrace τB hB ω trB).toLinearMap
      (constant τB hB ω trB).range ψ.range)
    (S : RealTracialSequence τR.toLinearMap)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    {b : ℝ} (Q : CanonicalSecondFrame τB hB ω trB ψ hψ b)
    (x : B) (hxstar : star x = x) (hxsq : x * x = 1) (hx0 : τB x = 0)
    (source_balls : ∀ C : ℝ, IsClosed (gnsTracialVector τB '' Metric.closedBall (0 : B) C))
    (published : CanonicalFreeCornerInput τB τR hB ω trB ψ hψτ hψ M Q x hxsq)
    (rounding : SpectralProjectionRoundingInput τA)
    (T : τB.GNS →L[ℂ] τB.GNS)
    (hcomm : ∀ a, T.comp (τB.gnsStarAlgHom (φ a)) =
      (τB.gnsStarAlgHom (φ a)).comp T)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcorner : ∀ (q : A) (hq : IsStarProjection q), (τA q).re ≤ b →
      ∀ z : CStarCorner (φ q) (hq.map φ),
        ‖commutator T (τB.gnsStarAlgHom (z : B))‖ ≤ ε * ‖z‖) :
    ‖commutator T (τB.gnsStarAlgHom x)‖ ≤ cornerConstant * ε := by
  sorry

end KadisonSimilarity

end

end OAI
end
