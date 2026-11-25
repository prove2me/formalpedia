-- Prove2me | Theorems.Thm_GlobalTheory_ThetaLin_sval_of_isTwistPull
-- name    : GlobalTheory.ThetaLin.sval_of_isTwistPull
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:40:02.464634+00:00
-- url     : https://prove2.me/theorems/fd0e4459-3e87-5d36-8801-3d28cd28e6ca
-- title:
--   Theta Lin: sval of is Twist Pull
-- statement:
--   The Theta Lin construction uses the sval of is Twist Pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SvalOfIsTwistPull.lean#L77-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SvalOfIsTwistPull.lean#L77-L94

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

theorem GlobalTheory.ThetaLin.sval_of_isTwistPull {s : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)}
    (H : IsTwistPull A L ψ m hm a b α s s') {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' r z J = (val α r z J).val * sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (r ≫ ψ.left) z J := by sorry
