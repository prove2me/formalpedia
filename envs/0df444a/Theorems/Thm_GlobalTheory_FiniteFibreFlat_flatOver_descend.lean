-- Prove2me | Theorems.Thm_GlobalTheory_FiniteFibreFlat_flatOver_descend
-- name    : GlobalTheory.FiniteFibreFlat.flatOver_descend
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:17:40.958913+00:00
-- url     : https://prove2.me/theorems/03078183-ea3a-4048-9fe8-b5478b29dc1f
-- title:
--   Finite Fibre Flat: flat Over descend
-- statement:
--   The Finite Fibre Flat construction uses the flat Over descend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FlatOfIsFiniteOfFlatGeometricFibres.lean#L139-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FlatOfIsFiniteOfFlatGeometricFibres.lean#L139-L149

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

theorem GlobalTheory.FiniteFibreFlat.flatOver_descend {S'' : Scheme.{0}} {g : Y ⟶ S} {t : S' ⟶ S} (σ : S'' ⟶ S')
    [Surjective σ] [Flat σ] [QuasiCompact σ] (H : FlatOver f g (σ ≫ t)) : FlatOver f g t := by sorry
