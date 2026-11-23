-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TraceDualDifferent_card_realEmb
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.card_realEmb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:11.56426+00:00
-- url     : https://prove2.me/theorems/00fe213e-0b04-4e1e-aa04-08c81c68a6da
-- title:
--   Trace Dual Different: card real Emb
-- statement:
--   The Trace Dual Different construction uses the card real Emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/TraceDualDifferent.lean#L77-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/TraceDualDifferent.lean#L77-L89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField nonZeroDivisors
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
variable {F : Type} [Field F] [NumberField F]
open NumberField nonZeroDivisors
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.card_realEmb [IsTotallyReal F] :
    Fintype.card (F →+* ℝ) = Module.finrank ℚ F := by sorry
