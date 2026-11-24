-- Prove2me | Theorems.Thm_GlobalTheory_DualBase_dualFormBase_of_value
-- name    : GlobalTheory.DualBase.dualFormBase_of_value
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:51:51.373804+00:00
-- url     : https://prove2.me/theorems/0f565468-82fa-4d07-b390-dc93c62181b2
-- title:
--   Dual Base: dual Form Base of value
-- statement:
--   The Dual Base construction uses the dual Form Base of value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DualFormBaseOfValue.lean#L8-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DualFormBaseOfValue.lean#L8-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualFormBaseOfValue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
open GlobalTheory GlobalTheory.DualBase

theorem GlobalTheory.DualBase.dualFormBase_of_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I]
    (φ : I → E →+* ℂ), IsCMType φ → DualFormValue φ → DualFormBase φ := by sorry
