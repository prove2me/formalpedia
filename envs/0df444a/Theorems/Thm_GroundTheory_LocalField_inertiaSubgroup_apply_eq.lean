-- Prove2me | Theorems.Thm_GroundTheory_LocalField_inertiaSubgroup_apply_eq
-- name    : GroundTheory.LocalField.inertiaSubgroup_apply_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:49:59.316302+00:00
-- url     : https://prove2.me/theorems/b0827c97-0f61-5b4a-8d58-42c6364967fe
-- title:
--   Local Field: inertia Subgroup apply eq
-- statement:
--   The Local Field construction uses the inertia Subgroup apply eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Unramified.lean#L155-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Unramified.lean#L155-L173

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Definitions.Def_GroundTheory_LocalFields_Unramified
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
open ValuativeRel IsLocalRing Polynomial
open scoped _root_.IntermediateField
open GroundTheory GroundTheory.LocalField
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem GroundTheory.LocalField.inertiaSubgroup_apply_eq (σ : L ≃ₐ[K] L) (hσ : σ ∈ inertiaSubgroup K L) (P : 𝒪[K][X])
    (γ : 𝒪[L]) (hγ : aeval γ P = 0) (hd : IsUnit (aeval γ (derivative P))) : σ γ = γ := by sorry
