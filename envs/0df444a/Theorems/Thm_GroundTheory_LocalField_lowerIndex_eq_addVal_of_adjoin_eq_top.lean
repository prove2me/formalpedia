-- Prove2me | Theorems.Thm_GroundTheory_LocalField_lowerIndex_eq_addVal_of_adjoin_eq_top
-- name    : GroundTheory.LocalField.lowerIndex_eq_addVal_of_adjoin_eq_top
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:51:44.620747+00:00
-- url     : https://prove2.me/theorems/7ce6d593-cdd8-4c86-b22f-f0e8ec068a38
-- title:
--   Local Field: lower Index eq add Val of adjoin eq top
-- statement:
--   The Local Field construction uses the lower Index eq add Val of adjoin eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndex.lean#L113-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndex.lean#L113-L124

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
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
open ValuativeRel IsLocalRing IsDiscreteValuationRing Polynomial
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}

theorem GroundTheory.LocalField.lowerIndex_eq_addVal_of_adjoin_eq_top {x : 𝒪[L]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤)
    (σ : L ≃ₐ[K] L) : lowerIndex K L σ = addVal 𝒪[L] (integerAlgEquiv K L σ x - x) := by sorry
