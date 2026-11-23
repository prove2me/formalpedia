-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TraceDualDifferent_mem_traceDual_iff
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.mem_traceDual_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:57.843117+00:00
-- url     : https://prove2.me/theorems/1352cb20-4830-482e-a506-08f19dad0d01
-- title:
--   Trace Dual Different: mem trace Dual iff
-- statement:
--   The Trace Dual Different construction uses the mem trace Dual iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/TraceDualDifferent.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/TraceDualDifferent.lean#L42-L47

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.mem_traceDual_iff {M : FractionalIdeal (𝓞 F)⁰ F} (hM : M ≠ 0) (y : F) :
    y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.traceDual M ↔ y ∈ FractionalIdeal.dual ℤ ℚ M := by sorry
