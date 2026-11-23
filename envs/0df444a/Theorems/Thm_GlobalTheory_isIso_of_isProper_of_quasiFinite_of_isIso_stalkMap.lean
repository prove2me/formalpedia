-- Prove2me | Theorems.Thm_GlobalTheory_isIso_of_isProper_of_quasiFinite_of_isIso_stalkMap
-- name    : GlobalTheory.isIso_of_isProper_of_quasiFinite_of_isIso_stalkMap
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:47.575344+00:00
-- url     : https://prove2.me/theorems/5c910285-97e5-4b05-9e6d-373ec87053ba
-- title:
--   Global Theory: is Iso of is Proper of quasi Finite of is Iso stalk Map
-- statement:
--   The Global Theory construction uses the is Iso of is Proper of quasi Finite of is Iso stalk Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveAlgebraMapIntegralClosureOfBirational.lean#L237-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveAlgebraMapIntegralClosureOfBirational.lean#L237-L246

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

theorem GlobalTheory.isIso_of_isProper_of_quasiFinite_of_isIso_stalkMap (f : X ⟶ Y) [IsProper f]
    [LocallyQuasiFinite f] [IsIntegral X] [IsIntegral Y] [IsDominant f]
    [IsIso (f.stalkMap (genericPoint X))]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) : IsIso f := by sorry
