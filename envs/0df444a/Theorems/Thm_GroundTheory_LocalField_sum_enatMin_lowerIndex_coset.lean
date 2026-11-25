-- Prove2me | Theorems.Thm_GroundTheory_LocalField_sum_enatMin_lowerIndex_coset
-- name    : GroundTheory.LocalField.sum_enatMin_lowerIndex_coset
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:51:11.278098+00:00
-- url     : https://prove2.me/theorems/91eb6b52-bafb-5e55-85d1-9e7296e36929
-- title:
--   Local Field: sum enat Min lower Index coset
-- statement:
--   The Local Field construction uses the sum enat Min lower Index coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UpperNumbering.lean#L122-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UpperNumbering.lean#L122-L150

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
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable [IsGalois K L] (M : IntermediateField K L) [IsGalois K M]

theorem GroundTheory.LocalField.sum_enatMin_lowerIndex_coset (σ : L ≃ₐ[K] L) {u : ℝ} (hu : -1 ≤ u) :
    ∑ τ : L ≃ₐ[M] L, enatMin (lowerIndex K L (σ * τ.restrictScalars K)) (u + 1) =
      ramificationIndex M L *
        enatMin (lowerIndex K M (AlgEquiv.restrictNormalHom M σ)) (herbrandPhi M L u + 1) := by sorry
