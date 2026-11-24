-- Prove2me | Theorems.Thm_GlobalTheory_tauBal_of_isPullDeg
-- name    : GlobalTheory.tauBal_of_isPullDeg
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:23:28.814819+00:00
-- url     : https://prove2.me/theorems/a2931248-1e24-4ef1-b62c-6a1863219e07
-- title:
--   Global Theory: tau Bal of is Pull Deg
-- statement:
--   The Global Theory construction uses the tau Bal of is Pull Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TauBalOfIsPullDeg.lean#L242-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TauBalOfIsPullDeg.lean#L242-L244

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBalOfIsPullDeg
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
noncomputable section
open GlobalTheory

theorem GlobalTheory.tauBal_of_isPullDeg : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (f g : D.P.A ⟶ D.P.A) (f' g' : D'.P.A ⟶ D'.P.A), IsMonHom f → IsMonHom g → RosatiAdj D.P.A D.P.L f g → f' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map f → g' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map g → ∀ (a b : D.X → D.X) (a' b' : D'.X → D'.X), (∀ y, hD.xe (a' y) = a (hD.xe y)) → (∀ y, hD.xe (b' y) = b (hD.xe y)) → (∀ y, D.c (a y) = D.c y ≫ f) → (∀ y, D.c (b y) = D.c y ≫ g) → D.TauBal f g a b → D'.TauBal f' g' a' b' := by sorry
