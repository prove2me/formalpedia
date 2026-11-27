-- Prove2me | Theorems.Thm_GlobalTheory_isOpenImmersion_and_isIso_of_quasiFinite_of_birational
-- name    : GlobalTheory.isOpenImmersion_and_isIso_of_quasiFinite_of_birational
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:47:19.592567+00:00
-- url     : https://prove2.me/theorems/b044ef47-0876-5678-bd94-dadef7e85b78
-- title:
--   Global Theory: is Open Immersion and is Iso of quasi Finite of birational
-- statement:
--   The Global Theory construction uses the is Open Immersion and is Iso of quasi Finite of birational property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveAlgebraMapIntegralClosureOfBirational.lean#L292-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveAlgebraMapIntegralClosureOfBirational.lean#L292-L299

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

theorem GlobalTheory.isOpenImmersion_and_isIso_of_quasiFinite_of_birational (f : X ⟶ Y) [IsSeparated f]
    [QuasiCompact f] [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsIntegral X] [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.Opens) (hU : Nonempty U) [IsIso (f ∣_ U)] :
    IsOpenImmersion f ∧ (IsFinite f → IsIso f) ∧ (IsProper f → IsIso f) := by sorry
