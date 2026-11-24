-- Prove2me | Theorems.Thm_GlobalTheory_range_subset_of_closedPoint_mem
-- name    : GlobalTheory.range_subset_of_closedPoint_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:14:41.837024+00:00
-- url     : https://prove2.me/theorems/071081a6-2cba-4f47-ba5c-097d444daa30
-- title:
--   Global Theory: range subset of closed Point mem
-- statement:
--   The Global Theory construction uses the range subset of closed Point mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L127-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L127-L132

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
variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}

theorem GlobalTheory.range_subset_of_closedPoint_mem (f : Spec (.of R) ⟶ X) {U : X.Opens}
    (hU : f (closedPoint R) ∈ U) : Set.range f ⊆ U := by sorry
