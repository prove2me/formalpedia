-- Prove2me | Theorems.Thm_GlobalTheory_TypeComplement_ne_bot_iff_toSubmodule
-- name    : GlobalTheory.TypeComplement.ne_bot_iff_toSubmodule
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:16:33.627584+00:00
-- url     : https://prove2.me/theorems/3cec133c-ef2c-484d-a7a8-f774a3a61b8a
-- title:
--   Type Complement: ne bot iff to Submodule
-- statement:
--   The Type Complement construction uses the ne bot iff to Submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsComplementWithoutCommonIrreducibleTypes.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsComplementWithoutCommonIrreducibleTypes.lean#L38-L43

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

theorem GlobalTheory.TypeComplement.ne_bot_iff_toSubmodule {S : Subrepresentation ρ} : S ≠ ⊥ ↔ S.toSubmodule ≠ ⊥ := by sorry
