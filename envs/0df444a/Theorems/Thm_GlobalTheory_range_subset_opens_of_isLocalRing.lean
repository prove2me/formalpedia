-- Prove2me | Theorems.Thm_GlobalTheory_range_subset_opens_of_isLocalRing
-- name    : GlobalTheory.range_subset_opens_of_isLocalRing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:39:02.64212+00:00
-- url     : https://prove2.me/theorems/89259564-53a0-4e25-94ad-7150e188b928
-- title:
--   Global Theory: range subset opens of is Local Ring
-- statement:
--   The Global Theory construction uses the range subset opens of is Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsCompletionPointClosedPointMemOfSmooth.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsCompletionPointClosedPointMemOfSmooth.lean#L17-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
variable {X S : Scheme.{u}} (f : X ⟶ S)

theorem GlobalTheory.range_subset_opens_of_isLocalRing {B : CommRingCat.{u}} [IsLocalRing B] (s : Spec B ⟶ S)
    {U : S.Opens} (h : s (closedPoint B) ∈ U) : Set.range s ⊆ U := by sorry
