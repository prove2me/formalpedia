-- Prove2me | Theorems.Thm_GlobalTheory_isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict
-- name    : GlobalTheory.isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:13.614482+00:00
-- url     : https://prove2.me/theorems/981660f1-2f10-44a5-8f86-a3a578f9a4eb
-- title:
--   Global Theory: is Open Immersion of quasi Finite of is Open Immersion restrict
-- statement:
--   The Global Theory construction uses the is Open Immersion of quasi Finite of is Open Immersion restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveAlgebraMapIntegralClosureOfBirational.lean#L277-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveAlgebraMapIntegralClosureOfBirational.lean#L277-L290

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

theorem GlobalTheory.isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict (f : X ⟶ Y) [IsSeparated f]
    [QuasiCompact f] [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsIntegral X] [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (V : X.Opens) (hV : Nonempty V) [IsOpenImmersion (V.ι ≫ f)] : IsOpenImmersion f := by sorry
