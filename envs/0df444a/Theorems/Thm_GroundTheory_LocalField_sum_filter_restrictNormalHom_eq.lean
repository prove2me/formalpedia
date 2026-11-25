-- Prove2me | Theorems.Thm_GroundTheory_LocalField_sum_filter_restrictNormalHom_eq
-- name    : GroundTheory.LocalField.sum_filter_restrictNormalHom_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:05:19.028363+00:00
-- url     : https://prove2.me/theorems/1523b65c-aced-5d94-a19f-1562f1c56396
-- title:
--   Local Field: sum filter restrict Normal Hom eq
-- statement:
--   The Local Field construction uses the sum filter restrict Normal Hom eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UpperNumbering.lean#L36-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UpperNumbering.lean#L36-L51

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandFunction
import Definitions.Def_GroundTheory_LocalFields_LowerIndexQuotient
import Definitions.Def_GroundTheory_LocalFields_UpperNumbering
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel
variable {K L : Type*} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L) [Normal K M]
open Classical

theorem GroundTheory.LocalField.sum_filter_restrictNormalHom_eq {β : Type*} [AddCommMonoid β] [Fintype (L ≃ₐ[K] L)]
    [Fintype (L ≃ₐ[M] L)] (F : (L ≃ₐ[K] L) → β) (σ : L ≃ₐ[K] L) :
    ∑ ρ ∈ Finset.univ.filter
        (fun ρ ↦ AlgEquiv.restrictNormalHom M ρ = AlgEquiv.restrictNormalHom M σ), F ρ =
      ∑ τ : L ≃ₐ[M] L, F (σ * τ.restrictScalars K) := by sorry
