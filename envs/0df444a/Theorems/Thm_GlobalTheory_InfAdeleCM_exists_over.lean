-- Prove2me | Theorems.Thm_GlobalTheory_InfAdeleCM_exists_over
-- name    : GlobalTheory.InfAdeleCM.exists_over
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:13.377874+00:00
-- url     : https://prove2.me/theorems/0103f236-e66c-4fce-a796-1fa97e41fb00
-- title:
--   Inf Adele CM: exists over
-- statement:
--   The Inf Adele CM construction uses the exists over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/InfAdeleTensorBijective.lean#L144-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/InfAdeleTensorBijective.lean#L144-L157

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

theorem GlobalTheory.InfAdeleCM.exists_over [IsTotallyReal F] (Ψ : Set (E →+* ℂ))
    (hΨ : ∀ τ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (w : InfinitePlace F) :
    ∃ τ ∈ Ψ, InfinitePlace.mk (τ.comp (algebraMap F E)) = w := by sorry
