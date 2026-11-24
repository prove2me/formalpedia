-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CompletedLStripBounds_archFactor_two_mul
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor_two_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:49.387808+00:00
-- url     : https://prove2.me/theorems/2934ed7c-6d9a-44a6-b6ea-598caa710f12
-- title:
--   Completed LStrip Bounds: arch Factor two mul
-- statement:
--   The Completed LStrip Bounds construction uses the arch Factor two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/CompletedLStripBounds.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/CompletedLStripBounds.lean#L44-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor_two_mul (m : I → ℤ) (s : ℂ) : archFactor (fun i => 2 * m i) s = LInf m s := by sorry
