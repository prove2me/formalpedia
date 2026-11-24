-- Prove2me | Theorems.Thm_GlobalTheory_isOpenImmersion_of_quasiFinite_of_birational
-- name    : GlobalTheory.isOpenImmersion_of_quasiFinite_of_birational
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:58:09.1088+00:00
-- url     : https://prove2.me/theorems/cc1a4bd9-be52-4ad1-93ea-7962c359a1fc
-- title:
--   Global Theory: is Open Immersion of quasi Finite of birational
-- statement:
--   The Global Theory construction uses the is Open Immersion of quasi Finite of birational property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveAlgebraMapIntegralClosureOfBirational.lean#L248-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveAlgebraMapIntegralClosureOfBirational.lean#L248-L253

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

theorem GlobalTheory.isOpenImmersion_of_quasiFinite_of_birational (f : X ⟶ Y) [IsSeparated f]
    [QuasiCompact f] [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsIntegral X] [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.Opens) (hU : Nonempty U) [IsIso (f ∣_ U)] : IsOpenImmersion f := by sorry
