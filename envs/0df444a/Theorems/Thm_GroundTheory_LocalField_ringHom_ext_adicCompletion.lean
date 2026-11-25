-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ringHom_ext_adicCompletion
-- name    : GroundTheory.LocalField.ringHom_ext_adicCompletion
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:18:59.152299+00:00
-- url     : https://prove2.me/theorems/2ab455f3-668b-5f6e-9848-7d3213edbe13
-- title:
--   Local Field: ring Hom ext adic Completion
-- statement:
--   The Local Field construction uses the ring Hom ext adic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompletedUnramified.lean#L170-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompletedUnramified.lean#L170-L184

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramifiedIntegers
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnitMulPowAdic
import Definitions.Def_GroundTheory_LocalFields_CompletedUnramified
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
open IsLocalRing ValuativeRel
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
local notation "𝔅" => AdicCompletion (maximalIdeal R) R

theorem GroundTheory.LocalField.ringHom_ext_adicCompletion {ϖ : R} (hϖ : Irreducible ϖ) {τ₁ τ₂ : 𝔅 →+* 𝔅}
    (h : ∀ r, τ₁ (algebraMap R 𝔅 r) = τ₂ (algebraMap R 𝔅 r))
    (hmem : τ₁ (algebraMap R 𝔅 ϖ) ∈ maximalIdeal 𝔅) : τ₁ = τ₂ := by sorry
