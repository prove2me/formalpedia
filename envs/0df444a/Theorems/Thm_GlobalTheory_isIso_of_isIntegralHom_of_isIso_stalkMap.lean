-- Prove2me | Theorems.Thm_GlobalTheory_isIso_of_isIntegralHom_of_isIso_stalkMap
-- name    : GlobalTheory.isIso_of_isIntegralHom_of_isIso_stalkMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:46.263773+00:00
-- url     : https://prove2.me/theorems/03e2ddf4-64e1-476a-8a50-fab3546383b7
-- title:
--   Global Theory: is Iso of is Integral Hom of is Iso stalk Map
-- statement:
--   The Global Theory construction uses the is Iso of is Integral Hom of is Iso stalk Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveAlgebraMapIntegralClosureOfBirational.lean#L227-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveAlgebraMapIntegralClosureOfBirational.lean#L227-L232

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

theorem GlobalTheory.isIso_of_isIntegralHom_of_isIso_stalkMap (f : X ⟶ Y) [IsIntegralHom f]
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [IsIso (f.stalkMap (genericPoint X))]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) : IsIso f := by sorry
