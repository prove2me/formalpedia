-- Prove2me | Theorems.Thm_GlobalTheory_exists_complete_isAlgClosed_isometry
-- name    : GlobalTheory.exists_complete_isAlgClosed_isometry
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:30:43.418334+00:00
-- url     : https://prove2.me/theorems/6173deb9-03cd-4162-81be-606d971def83
-- title:
--   Global Theory: exists complete is Alg Closed isometry
-- statement:
--   The Global Theory construction uses the exists complete is Alg Closed isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L285-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L285-L306

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u

theorem GlobalTheory.exists_complete_isAlgClosed_isometry (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] :
    ∃ (C : Type u) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C)
      (_ : IsAlgClosed C) (i : K →+* C), ∀ x, ‖i x‖ = ‖x‖ := by sorry
