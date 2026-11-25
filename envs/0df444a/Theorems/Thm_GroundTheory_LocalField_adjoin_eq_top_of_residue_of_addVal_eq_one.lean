-- Prove2me | Theorems.Thm_GroundTheory_LocalField_adjoin_eq_top_of_residue_of_addVal_eq_one
-- name    : GroundTheory.LocalField.adjoin_eq_top_of_residue_of_addVal_eq_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:15:02.500047+00:00
-- url     : https://prove2.me/theorems/000372e9-78f2-487b-a192-c4372c032959
-- title:
--   Local Field: adjoin eq top of residue of add Val eq one
-- statement:
--   The Local Field construction uses the adjoin eq top of residue of add Val eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Monogenic.lean#L22-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Monogenic.lean#L22-L74

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Definitions.Def_GroundTheory_LocalFields_Monogenic
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
open ValuativeRel Polynomial IsDiscreteValuationRing IsLocalRing
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable (K)

theorem GroundTheory.LocalField.adjoin_eq_top_of_residue_of_addVal_eq_one {x : 𝒪[L]}
    (hx : Algebra.adjoin 𝓀[K] {residue 𝒪[L] x} = ⊤) {π : 𝒪[L]}
    (hπA : π ∈ Algebra.adjoin 𝒪[K] {x}) (hπ : addVal 𝒪[L] π = 1) :
    Algebra.adjoin 𝒪[K] {x} = ⊤ := by sorry
