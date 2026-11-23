-- Prove2me | Theorems.Thm_GlobalTheory_LineCos_lineVec_ne_zero
-- name    : GlobalTheory.LineCos.lineVec_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:57.695439+00:00
-- url     : https://prove2.me/theorems/d0417e17-d787-4900-b681-30fa0c94c9ab
-- title:
--   Line Cos: line Vec ne zero
-- statement:
--   The Line Cos construction uses the line Vec ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOnCosSq.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOnCosSq.lean#L40-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Set Matrix
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LineCos

theorem GlobalTheory.LineCos.lineVec_ne_zero (s : Bool) (x : ℂ) : lineVec s x ≠ 0 := by sorry
