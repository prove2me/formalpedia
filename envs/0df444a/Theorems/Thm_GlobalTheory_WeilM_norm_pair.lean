-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_norm_pair
-- name    : GlobalTheory.WeilM.norm_pair
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:09.780805+00:00
-- url     : https://prove2.me/theorems/765d91e7-2b1d-4fb1-8078-19740e431cdc
-- title:
--   Weil M: norm pair
-- statement:
--   The Weil M construction uses the norm pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSplittingSplitOm.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSplittingSplitOm.lean#L29-L31

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

theorem GlobalTheory.WeilM.norm_pair (x : R × R) : Algebra.norm R x = x.1 * x.2 := by sorry
