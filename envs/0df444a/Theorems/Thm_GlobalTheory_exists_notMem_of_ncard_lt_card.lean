-- Prove2me | Theorems.Thm_GlobalTheory_exists_notMem_of_ncard_lt_card
-- name    : GlobalTheory.exists_notMem_of_ncard_lt_card
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:36:30.846476+00:00
-- url     : https://prove2.me/theorems/5bb886dc-ae73-4636-ba26-3432b92f1dbd
-- title:
--   Global Theory: exists not Mem of ncard lt card
-- statement:
--   The Global Theory construction uses the exists not Mem of ncard lt card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPairAvoidingSmallSets.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPairAvoidingSmallSets.lean#L9-L18

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPairAvoidingSmallSets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.exists_notMem_of_ncard_lt_card {H : Type} [Finite H] (S : Set H)
    (h : S.ncard < Nat.card H) : ∃ x : H, x ∉ S := by sorry
