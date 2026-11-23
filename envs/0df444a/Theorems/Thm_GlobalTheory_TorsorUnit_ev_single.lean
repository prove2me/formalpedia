-- Prove2me | Theorems.Thm_GlobalTheory_TorsorUnit_ev_single
-- name    : GlobalTheory.TorsorUnit.ev_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:26:29.933028+00:00
-- url     : https://prove2.me/theorems/e43bf48c-5cf5-4530-8cf3-486ff48fb634
-- title:
--   Torsor Unit: ev single
-- statement:
--   The Torsor Unit construction uses the ev single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLocalUnitOfWeight.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLocalUnitOfWeight.lean#L24-L26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorsorUnit
variable {X : Type} [AddCommGroup X] {A C R R' : Type} [CommRing A] [CommRing C] [CommRing R]
  [CommRing R']

theorem GlobalTheory.TorsorUnit.ev_single (θ : C →+* R) (φ : Multiplicative X →* Rˣ) (x : X) (c : C) :
    ev θ φ (AddMonoidAlgebra.single x c) = θ c * (φ (Multiplicative.ofAdd x)).val := by sorry
