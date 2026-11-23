-- Prove2me | Theorems.Thm_GlobalTheory_birational_of_isIso_morphismRestrict
-- name    : GlobalTheory.birational_of_isIso_morphismRestrict
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:15.038497+00:00
-- url     : https://prove2.me/theorems/6e6ee849-0881-4c78-9dd6-0eea75823022
-- title:
--   Global Theory: birational of is Iso morphism Restrict
-- statement:
--   The Global Theory construction uses the birational of is Iso morphism Restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveAlgebraMapIntegralClosureOfBirational.lean#L182-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveAlgebraMapIntegralClosureOfBirational.lean#L182-L195

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

theorem GlobalTheory.birational_of_isIso_morphismRestrict (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    (U : Y.Opens) (hU : Nonempty U) [IsIso (f ∣_ U)] :
    IsDominant f ∧ IsIso (f.stalkMap (genericPoint X)) := by sorry
