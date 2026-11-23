-- Prove2me | Theorems.Thm_GlobalTheory_ne_top_of_isHausdorff
-- name    : GlobalTheory.ne_top_of_isHausdorff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:08.683306+00:00
-- url     : https://prove2.me/theorems/6042648f-c8a7-49b3-b985-c4bb56dd4cf3
-- title:
--   Global Theory: ne top of is Hausdorff
-- statement:
--   The Global Theory construction uses the ne top of is Hausdorff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L229-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L229-L231

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {I}
variable [IsLocalRing R]

theorem GlobalTheory.ne_top_of_isHausdorff (I : Ideal R) [IsHausdorff I R] : I ≠ ⊤ := by sorry
