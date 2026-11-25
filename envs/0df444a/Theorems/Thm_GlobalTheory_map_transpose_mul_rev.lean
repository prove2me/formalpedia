-- Prove2me | Theorems.Thm_GlobalTheory_map_transpose_mul_rev
-- name    : GlobalTheory.map_transpose_mul_rev
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:28:36.98665+00:00
-- url     : https://prove2.me/theorems/170a9682-b25f-4715-a8ac-24e200c63e86
-- title:
--   Global Theory: map transpose mul rev
-- statement:
--   The Global Theory construction uses the map transpose mul rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/UnitaryStabiliserOrthogonalSummand.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/UnitaryStabiliserOrthogonalSummand.lean#L7-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitaryStabiliserOrthogonalSummand
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

theorem GlobalTheory.map_transpose_mul_rev {R : Type} [CommRing R] (s : R →+* R) {l m n : Type} [Fintype m]
    (A : Matrix l m R) (B : Matrix m n R) :
    ((A * B).map s)ᵀ = (B.map s)ᵀ * (A.map s)ᵀ := by sorry
