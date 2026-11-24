-- Prove2me | Theorems.Thm_GlobalTheory_WitnessData_comm_of_pullback
-- name    : GlobalTheory.WitnessData.comm_of_pullback
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:57:31.611966+00:00
-- url     : https://prove2.me/theorems/60704d63-b6c2-4008-bb18-e461fd80d770
-- title:
--   Witness Data: comm of pullback
-- statement:
--   The Witness Data construction uses the comm of pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataIsoOfTwoWitnesses.lean#L174-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataIsoOfTwoWitnesses.lean#L174-L193

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AdmissibleBasePowerSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataIsoOfTwoWitnesses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.WitnessData

theorem GlobalTheory.WitnessData.comm_of_pullback {S S₀ : Scheme.{0}} {B B' : Over S} {B₀ : Over S₀} {f : S ⟶ S₀} {i : S ⟶ S} (hi : i = 𝟙 S)
    {φ : B.left ⟶ B₀.left} (hφ : IsPullback φ B.hom B₀.hom f) (e : B' ⟶ (Over.pullback i).obj B)
    {φ' : B'.left ⟶ B₀.left} (hφ' : φ' = (e.left ≫ pullback.fst B.hom i) ≫ φ) {x : B ⟶ B} {x' : B' ⟶ B'}
    {x₀ : B₀.left ⟶ B₀.left} (h : x.left ≫ φ = φ ≫ x₀) (h' : x'.left ≫ φ' = φ' ≫ x₀) :
    x' ≫ e = e ≫ (Over.pullback i).map x := by sorry
