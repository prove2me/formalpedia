-- Prove2me | Theorems.Thm_GlobalTheory_svalAddHom_smul
-- name    : GlobalTheory.svalAddHom_smul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:24:05.031223+00:00
-- url     : https://prove2.me/theorems/4930ba28-e745-4057-a51e-6be21b1e593f
-- title:
--   Global Theory: sval Add Hom smul
-- statement:
--   The Global Theory construction uses the sval Add Hom smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSumTmulLinearIndependent.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSumTmulLinearIndependent.lean#L38-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparatedStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SmulOneSecEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSumTmulLinearIndependent
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
open GlobalTheory
variable {F : Type} [CommRing F] {Z Y T : Scheme.{0}} {L : LB Z} (p : Y ⟶ Spec (CommRingCat.of F))
  {K : Type} [Fintype K] (φ : K → (Y ⟶ Z)) (ε : K → ℤ)

theorem GlobalTheory.svalAddHom_smul (r : T ⟶ Y) (z : T) {J : (T ⟶ Z) → L.ι} (hJ : Good L z J) (c : F)
    (s : SecMod p (LB.LinComb L φ ε)) :
    svalAddHom p φ ε r z hJ (c • s) =
      gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * svalAddHom p φ ε r z hJ s := by sorry
