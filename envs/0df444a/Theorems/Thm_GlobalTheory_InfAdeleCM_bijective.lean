-- Prove2me | Theorems.Thm_GlobalTheory_InfAdeleCM_bijective
-- name    : GlobalTheory.InfAdeleCM.bijective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:27.26707+00:00
-- url     : https://prove2.me/theorems/2509f6ec-0bf6-4bf2-9f43-027cee946b51
-- title:
--   Inf Adele CM: bijective
-- statement:
--   The Inf Adele CM construction uses the bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/InfAdeleTensorBijective.lean#L159-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/InfAdeleTensorBijective.lean#L159-L215

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

theorem GlobalTheory.InfAdeleCM.bijective [IsTotallyReal F] (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hτ : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x))
    (θ : (E →+* ℂ) → (InfiniteAdeleRing F ⊗[F] E →+* ℂ))
    (hθ : ∀ τ a x, θ τ (a ⊗ₜ x) = ext (τ.comp (algebraMap F E)) a * τ x)
    (Ψ : Set (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) :
    Function.Bijective (fun (z : InfiniteAdeleRing F ⊗[F] E) (τ : Ψ) => θ τ.1 z) := by sorry
