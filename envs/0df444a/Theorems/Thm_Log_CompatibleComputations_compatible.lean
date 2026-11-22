-- Prove2me | Theorems.Thm_Log_CompatibleComputations_compatible
-- name    : Log.CompatibleComputations.compatible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:04:48.525752+00:00
-- url     : https://prove2.me/theorems/407c19b3-7f06-446d-90f4-bd0b40c1d4ad
-- title:
--   Compatible Computations: compatible
-- statement:
--   The compatibility proof.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Log.lean#L46-L47
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Log.lean#L46-L47

import Definitions.Def_EventStructures_Family_Computation
import Definitions.Def_EventStructures_Family_Log
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)
open Log
local infixl:50 " ⊨ " => compatibleWithLog F R

theorem Log.CompatibleComputations.compatible {l : Set F.Event}
    (σ : CompatibleComputations F R l) : CompatibleComputations.val F R σ ⊨ l := by sorry
