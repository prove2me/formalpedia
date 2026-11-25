-- Prove2me | Theorems.Thm_GlobalTheory_DegPull_exists_isPullDeg
-- name    : GlobalTheory.DegPull.exists_isPullDeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:22.761917+00:00
-- url     : https://prove2.me/theorems/e2d80762-5feb-450d-9093-c93c9652c3f8
-- title:
--   Deg Pull: exists is Pull Deg
-- statement:
--   The Deg Pull construction uses the exists is Pull Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/NonemptyCubicalPull.lean#L196-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/NonemptyCubicalPull.lean#L196-L265

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.DegPull

theorem GlobalTheory.DegPull.exists_isPullDeg (hP : PolBaseChangeSt) (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    (φ : R →+* R') (D : DegPre R) (W : (Spec (CommRingCat.of R)).Opens) (hW : Nonempty (PsiOn D W))
    (hη : (specOf φ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ W) :
    ∃ (D' : DegPre R') (hD : IsPullDeg φ D D'), hD.W = W ∧ D'.P.g = D.P.g := by sorry
