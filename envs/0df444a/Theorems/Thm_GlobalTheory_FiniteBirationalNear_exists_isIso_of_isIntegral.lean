-- Prove2me | Theorems.Thm_GlobalTheory_FiniteBirationalNear_exists_isIso_of_isIntegral
-- name    : GlobalTheory.FiniteBirationalNear.exists_isIso_of_isIntegral
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:29:52.785542+00:00
-- url     : https://prove2.me/theorems/69cd1a15-398b-47be-8e47-b2e0ee5ce2d1
-- title:
--   Finite Birational Near: exists is Iso of is Integral
-- statement:
--   The Finite Birational Near construction uses the exists is Iso of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoNearNormalPointOfFiniteBirational.lean#L87-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoNearNormalPointOfFiniteBirational.lean#L87-L141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoNearNormalPointOfFiniteBirational
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open GlobalTheory GlobalTheory.FiniteBirationalNear

theorem GlobalTheory.FiniteBirationalNear.exists_isIso_of_isIntegral {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [IsIntegral X]
    [IsIntegral Y] [IsDominant f] [IsIso (f.stalkMap (genericPoint X))] (y : Y)
    [IsIntegrallyClosed (Y.presheaf.stalk y)] : ∃ V : Y.Opens, y ∈ V ∧ IsIso (f ∣_ V) := by sorry
