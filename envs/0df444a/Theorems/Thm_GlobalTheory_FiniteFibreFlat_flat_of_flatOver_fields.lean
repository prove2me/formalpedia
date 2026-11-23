-- Prove2me | Theorems.Thm_GlobalTheory_FiniteFibreFlat_flat_of_flatOver_fields
-- name    : GlobalTheory.FiniteFibreFlat.flat_of_flatOver_fields
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:52.759806+00:00
-- url     : https://prove2.me/theorems/945c9935-480a-4e0c-9102-9fd96f9a49fc
-- title:
--   Finite Fibre Flat: flat of flat Over fields
-- statement:
--   The Finite Fibre Flat construction uses the flat of flat Over fields property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FlatOfIsFiniteOfFlatGeometricFibres.lean#L152-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FlatOfIsFiniteOfFlatGeometricFibres.lean#L152-L205

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFlatFibresDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatOfIsFiniteOfFlatGeometricFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.FiniteFibreFlat
open TensorProduct IsLocalRing
open FibreFlat
variable {X Y S S' : Scheme.{0}} {f : X ⟶ Y}
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.FiniteFibreFlat.flat_of_flatOver_fields (f : X ⟶ Y) (g : Y ⟶ S) (hY : IsLocallyNoetherian Y)
    (h1 : Flat (f ≫ g)) (h2 : IsFinite f)
    (H : ∀ (k : Type) [Field k] (t : Spec (CommRingCat.of k) ⟶ S), FlatOver f g t) :
    Flat f := by sorry
