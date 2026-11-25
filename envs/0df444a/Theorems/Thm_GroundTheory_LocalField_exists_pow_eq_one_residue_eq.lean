-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_pow_eq_one_residue_eq
-- name    : GroundTheory.LocalField.exists_pow_eq_one_residue_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:44:29.584103+00:00
-- url     : https://prove2.me/theorems/a54d4efb-c854-48f9-86a9-f84858d74843
-- title:
--   Local Field: exists pow eq one residue eq
-- statement:
--   The Local Field construction uses the exists pow eq one residue eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedRootsOfUnity.lean#L17-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedRootsOfUnity.lean#L17-L41

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

theorem GroundTheory.LocalField.exists_pow_eq_one_residue_eq {m : ℕ} (hm : (m : 𝓀[L]) ≠ 0) {a : 𝓀[L]} (ha : a ^ m = 1) :
    ∃ x : 𝒪[L], x ^ m = 1 ∧ IsLocalRing.residue 𝒪[L] x = a := by sorry
