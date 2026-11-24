-- Prove2me | Theorems.Thm_GlobalTheory_IrreducibleGeneralizations_main
-- name    : GlobalTheory.IrreducibleGeneralizations.main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:40.701421+00:00
-- url     : https://prove2.me/theorems/0abcd04b-d822-4a92-ab1c-bebe22002d39
-- title:
--   Irreducible Generalizations: main
-- statement:
--   The Irreducible Generalizations construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIrreducibleGeneralizations.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIrreducibleGeneralizations.lean#L26-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIrreducibleGeneralizations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.IrreducibleGeneralizations
open AlgebraicGeometry Topology

theorem GlobalTheory.IrreducibleGeneralizations.main : ∀ {X : AlgebraicGeometry.Scheme} {x : ↥X} [IsDomain (↑(TopCat.Presheaf.stalk (AlgebraicGeometry.PresheafedSpace.presheaf (AlgebraicGeometry.SheafedSpace.toPresheafedSpace (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace (AlgebraicGeometry.Scheme.toLocallyRingedSpace X)))) x) : Type u_1)] {Z W : Set ↥X}, Z ∈ irreducibleComponents ↥X → W ∈ irreducibleComponents ↥X → x ∈ Z → x ∈ W → Z = W := by sorry
