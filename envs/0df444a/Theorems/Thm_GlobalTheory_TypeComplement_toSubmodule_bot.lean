-- Prove2me | Theorems.Thm_GlobalTheory_TypeComplement_toSubmodule_bot
-- name    : GlobalTheory.TypeComplement.toSubmodule_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:25.205986+00:00
-- url     : https://prove2.me/theorems/6bc3ce34-57a9-4648-beae-0ec15fd8e7b2
-- title:
--   Type Complement: to Submodule bot
-- statement:
--   The Type Complement construction uses the to Submodule bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsComplementWithoutCommonIrreducibleTypes.lean#L36-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsComplementWithoutCommonIrreducibleTypes.lean#L36-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsComplementWithoutCommonIrreducibleTypes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.TypeComplement
variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}

theorem GlobalTheory.TypeComplement.toSubmodule_bot : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := by sorry
