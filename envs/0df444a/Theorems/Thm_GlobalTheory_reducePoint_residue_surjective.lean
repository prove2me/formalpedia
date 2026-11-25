-- Prove2me | Theorems.Thm_GlobalTheory_reducePoint_residue_surjective
-- name    : GlobalTheory.reducePoint_residue_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:03:34.800286+00:00
-- url     : https://prove2.me/theorems/d93c09f7-3368-46a5-be6a-0b3764a00571
-- title:
--   Global Theory: reduce Point residue surjective
-- statement:
--   The Global Theory construction uses the reduce Point residue surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsCompletionPointClosedPointMemOfSmooth.lean#L190-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsCompletionPointClosedPointMemOfSmooth.lean#L190-L192

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
variable (B : Type u) [CommRing B] [HenselianLocalRing B] (s : Spec (.of B) ⟶ S)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (B : Type u) [CommRing B] [HenselianLocalRing B] (s : Spec (.of B) ⟶ S)

theorem GlobalTheory.reducePoint_residue_surjective [Smooth f] :
    Function.Surjective (_root_.GlobalTheory.reducePoint f (CommRingCat.ofHom (residue B)) s) := by sorry
