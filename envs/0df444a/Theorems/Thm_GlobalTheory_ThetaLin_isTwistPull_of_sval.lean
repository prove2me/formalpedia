-- Prove2me | Theorems.Thm_GlobalTheory_ThetaLin_isTwistPull_of_sval
-- name    : GlobalTheory.ThetaLin.isTwistPull_of_sval
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:29:32.445617+00:00
-- url     : https://prove2.me/theorems/e2682bee-e7d5-4375-9639-02f526da9e12
-- title:
--   Theta Lin: is Twist Pull of sval
-- statement:
--   The Theta Lin construction uses the is Twist Pull of sval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SvalOfIsTwistPull.lean#L96-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SvalOfIsTwistPull.lean#L96-L123

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_FinrankComplexReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalOfIsTwistPull
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
open GlobalTheory GlobalTheory.ThetaLin
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
  {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
  {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}

theorem GlobalTheory.ThetaLin.isTwistPull_of_sval (hL : L.IsLB) (hα : α.IsGen) {s : LB.Sec (LPow A L b T)}
    {s' : LB.Sec (LPow A L a T)}
    (H : ∀ y J, Good L y J → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) y J = (val α (𝟙 _) y J).val * sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) y J) :
    IsTwistPull A L ψ m hm a b α s s' := by sorry
