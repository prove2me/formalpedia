-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TraceDualDifferent_mem_traceDual_iff_different
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.mem_traceDual_iff_different
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:10:29.885176+00:00
-- url     : https://prove2.me/theorems/41a8d73a-9351-427e-9b7f-71058730c399
-- title:
--   Trace Dual Different: mem trace Dual iff different
-- statement:
--   The Trace Dual Different construction uses the mem trace Dual iff different property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/TraceDualDifferent.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/TraceDualDifferent.lean#L49-L51

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.mem_traceDual_iff_different {M : FractionalIdeal (𝓞 F)⁰ F} (hM : M ≠ 0) (y : F) :
    y ∈ traceDual M ↔ y ∈ ((differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F))⁻¹ * M⁻¹ := by sorry
