-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_Stages_stage
-- name    : GlobalTheory.SmGL.Stages.stage
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:57.366802+00:00
-- url     : https://prove2.me/theorems/dd205684-8967-4d32-89e8-16f39b455452
-- title:
--   Stages: stage
-- statement:
--   The Stages construction uses the stage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyInv.lean#L122-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyInv.lean#L122-L191

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Topology Filter
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Stages
variable {F G M W X Y Z : Type} [Field F] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group M] [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup W] [Module F W]
  [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y] [AddCommGroup Z] [Module F Z]

theorem GlobalTheory.SmGL.Stages.stage {Q R : Subgroup G} (hRQ : R ≤ Q) {P : Subgroup M} (ℓ : Q →* M) (s : M →* Q)
    (hs : Continuous s) (hls : ∀ m, ℓ (s m) = m) (hR : ∀ q : Q, (q : G) ∈ R ↔ ℓ q ∈ P)
    {K : Set M} (hK : IsCompact K) (hPK : ∀ m, ∃ p : P, ∃ c ∈ K, m = p * c)
    (σ : Representation F P W) (τ : Representation F Q X) (hτ : ∀ᶠ u in 𝓝 (1 : M), τ (s u) = 1)
    (Θ : Representation F Q Y) (j : Y ≃ₗ[F] smoothPart (ind P σ) ⊗[F] X)
    (hj : ∀ q y, j (Θ q y) = TensorProduct.map (smInd P σ (ℓ q)) (τ q) (j y))
    (ρ : Representation F R Z) (i : W ⊗[F] X ≃ₗ[F] Z)
    (hi : ∀ (q : Q) (h : (q : G) ∈ R) z,
      ρ ⟨q, h⟩ (i z) = i (TensorProduct.map (σ ⟨ℓ q, (hR q).1 h⟩) (τ q) z)) :
    Nonempty ((smInd Q Θ).Equiv (smInd R ρ)) := by sorry
