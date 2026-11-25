-- Prove2me | Theorems.Thm_GlobalTheory_psiScal_eq_ratio
-- name    : GlobalTheory.psiScal_eq_ratio
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:15:25.398134+00:00
-- url     : https://prove2.me/theorems/dbc12f5a-6f2e-5891-86e1-4ccac832d7f1
-- title:
--   Global Theory: psi Scal eq ratio
-- statement:
--   The Global Theory construction uses the psi Scal eq ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PsiScalarEqExpansionCoefRatio.lean#L35-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PsiScalarEqExpansionCoefRatio.lean#L35-L77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SecCmp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsMulPullSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_JKAppTopInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PsiScalarEqExpansionCoefRatio
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
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
open GlobalTheory

theorem GlobalTheory.psiScal_eq_ratio : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (th : SecBT D (𝟙_ _) 1 0), PsiScal D ga a → PsiRel D (𝟙_ _) f → FibNZ (𝟙_ _ ⊗ D.P.A).hom th → ∀ (χ : D.X) (q p : R), Mult D th (f 0) q → Coef D χ (ga χ) th (f χ) p → algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) p := by sorry
