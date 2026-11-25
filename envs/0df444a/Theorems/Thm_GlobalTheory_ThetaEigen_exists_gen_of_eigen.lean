-- Prove2me | Theorems.Thm_GlobalTheory_ThetaEigen_exists_gen_of_eigen
-- name    : GlobalTheory.ThetaEigen.exists_gen_of_eigen
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T15:49:37.963901+00:00
-- url     : https://prove2.me/theorems/e148f31e-49c8-5cb2-ab38-8fee8351014d
-- title:
--   Theta Eigen: exists gen of eigen
-- statement:
--   The Theta Eigen construction uses the exists gen of eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ThetaOperatorPointZeroOfPowerEigen.lean#L45-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ThetaOperatorPointZeroOfPowerEigen.lean#L45-L84

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitOfStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalOfIsTwistPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsIntegralTensorLeftOfSmoothGrpObj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsIsGenOfInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ThetaOperatorPointZeroOfPowerEigen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.ThetaEigen

theorem GlobalTheory.ThetaEigen.exists_gen_of_eigen {X Y : Scheme.{0}} [IsIntegral Y] (hN : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    {L : LB X} (hL : L.IsLB) (pr m : Y ⟶ X) (τ : Y ⟶ Y) (hm : τ ≫ pr = m) (l : ℕ) (hl : 1 ≤ l)
    (th : LB.Sec (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => ((1 : ℕ) : ℤ))))
    (t : LB.Sec (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => (l : ℤ)))) (h0 : ∃ j, th.f j ≠ 0)
    (hp : ∀ y J, Good L y J → sval t (𝟙 Y) y J = sval th (𝟙 Y) y J ^ l) (c : Γ(Y, ⊤)ˣ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![pr, m] ![(l : ℤ), -(l : ℤ)])) (hα : α.IsGen)
    (H : ∀ y J, Good L y J →
      gs (𝟙 Y) y ⊤ c.val * sval t (𝟙 Y) y J = (val α (𝟙 Y) y J).val * sval t (𝟙 Y ≫ τ) y J) :
    ∃ r : LB.Gen (LB.LinComb L (K := Fin 2) ![m, pr] ![1, -1]), r.IsGen := by sorry
