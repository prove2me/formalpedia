-- Prove2me | Theorems.Thm_GlobalTheory_GaussExt_ii_sq
-- name    : GlobalTheory.GaussExt.ii_sq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:27:15.715868+00:00
-- url     : https://prove2.me/theorems/9e34d10b-aee5-4899-ba4f-8b29b0c947b1
-- title:
--   Gauss Ext: ii sq
-- statement:
--   The Gauss Ext construction uses the ii sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleXSqAddOne.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleXSqAddOne.lean#L36-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleXSqAddOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
noncomputable section
open GlobalTheory GlobalTheory.GaussExt
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

theorem GlobalTheory.GaussExt.ii_sq : ii F ^ 2 = -1 := by sorry
