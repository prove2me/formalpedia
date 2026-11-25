-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_isPrimitiveRoot_card_residueField_sub_one
-- name    : GroundTheory.LocalField.exists_isPrimitiveRoot_card_residueField_sub_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:54.470261+00:00
-- url     : https://prove2.me/theorems/9e50e514-e96b-4514-aa54-9bc8fc24eb1e
-- title:
--   Local Field: exists is Primitive Root card residue Field sub one
-- statement:
--   The Local Field construction uses the exists is Primitive Root card residue Field sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedRootsOfUnity.lean#L68-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedRootsOfUnity.lean#L68-L77

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
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
open ValuativeRel Polynomial
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem GroundTheory.LocalField.exists_isPrimitiveRoot_card_residueField_sub_one :
    ∃ ζ : 𝒪[L], IsPrimitiveRoot ζ (Nat.card 𝓀[L] - 1) := by sorry
