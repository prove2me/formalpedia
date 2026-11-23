-- Prove2me | Theorems.Thm_GlobalTheory_range_fst_residue
-- name    : GlobalTheory.range_fst_residue
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:50:26.1748+00:00
-- url     : https://prove2.me/theorems/f6c16b28-4ca6-4e68-9bdb-6dc945b55a49
-- title:
--   Global Theory: range fst residue
-- statement:
--   The Global Theory construction uses the range fst residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsCompletionPointClosedPointMemOfSmooth.lean#L257-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsCompletionPointClosedPointMemOfSmooth.lean#L257-L272

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
variable {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
variable {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]

theorem GlobalTheory.range_fst_residue {B : Type u} [CommRing B] [IsLocalRing B] (g : X ⟶ Spec (.of B)) :
    Set.range (pullback.fst g (Spec.map (CommRingCat.ofHom (residue B)))) =
      g ⁻¹' {closedPoint B} := by sorry
