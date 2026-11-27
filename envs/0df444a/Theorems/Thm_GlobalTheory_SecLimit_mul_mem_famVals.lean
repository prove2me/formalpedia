-- Prove2me | Theorems.Thm_GlobalTheory_SecLimit_mul_mem_famVals
-- name    : GlobalTheory.SecLimit.mul_mem_famVals
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T06:22:59.972041+00:00
-- url     : https://prove2.me/theorems/5ee4d56c-c69c-5c28-92be-ec2019eabe53
-- title:
--   Sec Limit: mul mem fam Vals
-- statement:
--   The Sec Limit construction uses the mul mem fam Vals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUniqueTwistedSectionOfCompatibleLevels.lean#L36-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUniqueTwistedSectionOfCompatibleLevels.lean#L36-L62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueLimit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueTwistedSectionOfCompatibleLevels
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
open GlobalTheory GlobalTheory.SecLimit
variable {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (k : ℕ) (α : D.X)
variable {D k α}

theorem GlobalTheory.SecLimit.mul_mem_famVals (u : LB.Gen (LB.LinComb D.P.L (ptφ D α) ![-1, 1])) (hu : u.IsGen)
    (T : Over (Spec (CommRingCat.of V))) {Y : Scheme.{0}} (h : Y ⟶ (T ⊗ D.P.A).left) {π : Y ⟶ D.P.A.left}
    (hπ : h ≫ (snd T D.P.A).left = π) (w : Vals D.P.L Y) :
    w * evU (LB.pullGen D.P.L _ _ u (π ≫ D.P.A.hom)) ∈ famVals D k α π ↔
      w ∈ secVals D.P.L (fun j => h ≫ twφ D α T j) ![(k : ℤ) - 1, 1] := by sorry
