-- Prove2me | Theorems.Thm_GlobalTheory_PsiInt_psiRel_integral
-- name    : GlobalTheory.PsiInt.psiRel_integral
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:28:28.464796+00:00
-- url     : https://prove2.me/theorems/8617eafd-ff3e-4be9-be2d-c44c3952da1b
-- title:
--   Psi Int: psi Rel integral
-- statement:
--   The Psi Int construction uses the psi Rel integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/JKAppTopInjective.lean#L105-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/JKAppTopInjective.lean#L105-L139

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecRelationDefect
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfSvalWhiskerRightEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_JKAppTopInjective
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
open GlobalTheory GlobalTheory.PsiInt
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem GlobalTheory.PsiInt.psiRel_integral : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ) (f : ∀ α, SecBT D (𝟙_ _) 1 α), PsiScal D ga a → PsiRel D (𝟙_ _) f → ∀ (χ : D.X) (p q : R), algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) p → ∀ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → gs (𝟙 _) z ⊤ (scal T.hom q) * sval (f χ) (lift (toUnit T) y).left z J = gs (𝟙 _) z ⊤ (scal T.hom p) * ((val (ga χ) (toUnit T).left z J * rigV D z J).val * sval (f 0) (lift (toUnit T) (y * cT D T χ)).left z J) := by sorry
