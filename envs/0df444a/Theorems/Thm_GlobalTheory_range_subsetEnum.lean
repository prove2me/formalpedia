-- Prove2me | Theorems.Thm_GlobalTheory_range_subsetEnum
-- name    : GlobalTheory.range_subsetEnum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:10.35683+00:00
-- url     : https://prove2.me/theorems/a83e8181-93f2-482b-8241-968408ca3935
-- title:
--   Global Theory: range subset Enum
-- statement:
--   The Global Theory construction uses the range subset Enum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MulConjTransposeEqOneOfOrthonormal.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MulConjTransposeEqOneOfOrthonormal.lean#L14-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
variable {R : Type*} [CommRing R]

theorem GlobalTheory.range_subsetEnum {n : Type*} [LinearOrder n] {i : ℕ} (S : Set.powersetCard n i) :
    Set.range (subsetEnum S) = (S.1 : Set n) := by sorry
