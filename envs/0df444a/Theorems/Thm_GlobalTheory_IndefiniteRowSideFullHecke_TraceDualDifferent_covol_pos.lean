-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TraceDualDifferent_covol_pos
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol_pos
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:15:41.581296+00:00
-- url     : https://prove2.me/theorems/c4858c4b-e5ec-4b16-85be-50c2c0ea5636
-- title:
--   Trace Dual Different: covol pos
-- statement:
--   The Trace Dual Different construction uses the covol pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/TraceDualDifferent.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/TraceDualDifferent.lean#L56-L60

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol_pos {M : FractionalIdeal (𝓞 F)⁰ F} (hM : M ≠ 0) :
    0 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol M := by sorry
