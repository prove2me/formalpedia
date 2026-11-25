-- Prove2me | Theorems.Thm_GlobalTheory_exists_degData_isPullDeg
-- name    : GlobalTheory.exists_degData_isPullDeg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:31:18.18869+00:00
-- url     : https://prove2.me/theorems/ed126178-bfc7-4232-8da5-927b7da7ada3
-- title:
--   Global Theory: exists deg Data is Pull Deg
-- statement:
--   The Global Theory construction uses the exists deg Data is Pull Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsDegDataIsPullDeg.lean#L21-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsDegDataIsPullDeg.lean#L21-L35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValEqOfAppInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiInOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsDegDataIsPullDeg
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
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.exists_degData_isPullDeg : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolBaseChangeSt → _root_.ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R'), I.map φ ≤ I' → ∀ (D : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegData R I) (W : (Spec (CommRingCat.of R)).Opens), Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Out.PsiOn D.toPre W) → (_root_.ReciprocityTheory.ChartRestriction.G.Out.specOf φ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ W → ∃ (D' : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegData R' I') (hD : _root_.ReciprocityTheory.ChartRestriction.G.Out.IsPullDeg φ D.toPre D'.toPre), hD.W = W ∧ D'.toPre.P.g = D.toPre.P.g := by sorry
