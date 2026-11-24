-- Prove2me | Theorems.Thm_GlobalTheory_isIso_of_isFinite_of_birational
-- name    : GlobalTheory.isIso_of_isFinite_of_birational
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:32.744793+00:00
-- url     : https://prove2.me/theorems/4dfbcfdb-09e6-4e80-a69e-e2b5d3e708a9
-- title:
--   Global Theory: is Iso of is Finite of birational
-- statement:
--   The Global Theory construction uses the is Iso of is Finite of birational property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveAlgebraMapIntegralClosureOfBirational.lean#L258-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveAlgebraMapIntegralClosureOfBirational.lean#L258-L262

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
open GlobalTheory
universe u
variable {X Y : Scheme.{u}}
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
variable {X Y : Scheme.{u}}

theorem GlobalTheory.isIso_of_isFinite_of_birational (f : X ⟶ Y) [IsFinite f]
    [IsIntegral X] [IsIntegral Y] (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.Opens) (hU : Nonempty U) [IsIso (f ∣_ U)] : IsIso f := by sorry
