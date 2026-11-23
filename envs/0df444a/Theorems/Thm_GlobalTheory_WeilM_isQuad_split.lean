-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_isQuad_split
-- name    : GlobalTheory.WeilM.isQuad_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:06.019049+00:00
-- url     : https://prove2.me/theorems/5cc5ddba-f013-437f-a046-569babb4f6d2
-- title:
--   Weil M: is Quad split
-- statement:
--   The Weil M construction uses the is Quad split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSplittingSplitOm.lean#L33-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSplittingSplitOm.lean#L33-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped NNReal Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R]

theorem GlobalTheory.WeilM.isQuad_split [Invertible (2 : R)] : IsQuad (swapA R) ((1, -1) : R × R) := by sorry
