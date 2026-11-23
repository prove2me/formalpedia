-- Prove2me | Theorems.Thm_GlobalTheory_HeckeStrip_norm_wt
-- name    : GlobalTheory.HeckeStrip.norm_wt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:58.928892+00:00
-- url     : https://prove2.me/theorems/51914cef-dcd2-46a5-a655-49f7cdd13116
-- title:
--   Hecke Strip: norm wt
-- statement:
--   The Hecke Strip construction uses the norm wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormWt.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormWt.lean#L28-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open GlobalTheory GlobalTheory.HeckeStrip
variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]

theorem GlobalTheory.HeckeStrip.norm_wt (φ : I → K →+* ℂ) (n : I → ℤ) {a : K} (ha : a ≠ 0) : ‖wt φ n a‖ = 1 := by sorry
