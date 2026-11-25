-- Prove2me | Theorems.Thm_GlobalTheory_IsoDesc_Eqns_ker
-- name    : GlobalTheory.IsoDesc.Eqns.ker
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:47:17.210794+00:00
-- url     : https://prove2.me/theorems/b2c6a206-e65c-5f03-9a6f-79caa31e2eb3
-- title:
--   Eqns: ker
-- statement:
--   The Eqns construction uses the ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsCPMapDescends.lean#L243-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsCPMapDescends.lean#L243-L258

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsCPMapDescends
import Theorems.Thm_GlobalTheory_UU_IsWt_mul

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
open GlobalTheory GlobalTheory.IsoDesc
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G B' : Over S'} {B : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj B']
  [IsCommMonObj B'] [GrpObj B] [IsCommMonObj B] {P : CP G} {M' : CP B'} {M : CP B} {q : G ⟶ B'}
  {β : B'.left ⟶ B.left} {hβ : β ≫ B.hom = B'.hom ≫ f}

theorem GlobalTheory.IsoDesc.Eqns.ker (mul : ∀ (T : Over S') (x y : T ⟶ B'), toBase hβ (x * y) = toBase hβ x * toBase hβ y)
    {T : Over S'} {z : T.left} {I J} (hI : Good M'.L.L z I) (hJ : Good M.L.L z J) {A : Type} [Group A]
    {π : A → (T ⟶ B')} {V : A → (T.left.presheaf.stalk z)ˣ} (h : Eqns M' M hβ z I J π V) {t : A} (ht : π t = 1) :
    V t = V t⁻¹ ∧ ∀ y u, V (t * y) * V (t * u) * V (y * u) * V 1 = V (t * y * u) * V t * V y * V u := by sorry
