-- Prove2me | Theorems.Thm_GlobalTheory_InfAdeleCM_infAdele_tensor_bijective
-- name    : GlobalTheory.InfAdeleCM.infAdele_tensor_bijective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:33.06312+00:00
-- url     : https://prove2.me/theorems/d61bda0a-aa86-41b6-b967-5070a8cb0a5e
-- title:
--   Inf Adele CM: inf Adele tensor bijective
-- statement:
--   The Inf Adele CM construction uses the inf Adele tensor bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/InfAdeleTensorBijective.lean#L217-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/InfAdeleTensorBijective.lean#L217-L232

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
open GlobalTheory GlobalTheory.InfAdeleCM
variable {F : Type} [Field F] [NumberField F]
variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem GlobalTheory.InfAdeleCM.infAdele_tensor_bijective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → IsTotallyReal F → (∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x)) → letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) := moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E); (∀ τ : E →+* ℂ, ∃ θ : InfiniteAdeleRing F ⊗[F] E →+* ℂ, (∀ x, θ (1 ⊗ₜ x) = τ x) ∧ Continuous fun a : InfiniteAdeleRing F => θ (a ⊗ₜ (1 : E))) ∧ ∀ θ : (E →+* ℂ) → (InfiniteAdeleRing F ⊗[F] E →+* ℂ), (∀ τ, (∀ x, θ τ (1 ⊗ₜ x) = τ x) ∧ Continuous fun a : InfiniteAdeleRing F => θ τ (a ⊗ₜ (1 : E))) → (∀ τ, Continuous (θ τ)) ∧ (∀ τ z, θ τ (sg (InfiniteAdeleRing F) c z) = starRingEnd ℂ (θ τ z)) ∧ ∀ Ψ : Set (E →+* ℂ), (∀ τ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → Function.Bijective (fun (z : InfiniteAdeleRing F ⊗[F] E) (τ : Ψ) => θ τ.1 z) := by sorry
