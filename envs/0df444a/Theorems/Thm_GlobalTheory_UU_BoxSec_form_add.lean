-- Prove2me | Theorems.Thm_GlobalTheory_UU_BoxSec_form_add
-- name    : GlobalTheory.UU.BoxSec.form_add
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:47:58.319808+00:00
-- url     : https://prove2.me/theorems/cb0030fc-79ee-593c-a4b4-507582631dbc
-- title:
--   Box Sec: form add
-- statement:
--   The Box Sec construction uses the form add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RepSymInv.lean#L174-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RepSymInv.lean#L174-L186

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RepSymInv
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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.BoxSec
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {Y : Over (Spec (CommRingCat.of R))}

theorem GlobalTheory.UU.BoxSec.form_add {U : Type} [CommGroup U] (h : (Y.left ⟶ D.P.A.left) → U) (x y a b c : Y ⟶ D.P.A) (hc : c * b = a) :
    cubP D h x y y⁻¹ * ((h (y⁻¹).left)⁻¹ * h y.left) * (h (1 : Y ⟶ D.P.A).left * h (1 : Y ⟶ D.P.A).left) *
      cubP D h a b x * cubP D h b y y⁻¹ * ((cubP D h a x y)⁻¹ * (cubP D h b x y⁻¹)⁻¹ * (cubP D h c b y)⁻¹) *
      ((h (x * y).left ^ (((1 : ℕ) : ℤ) - 1) * h (x * y * a).left * (h a.left)⁻¹ * h (1 : Y ⟶ D.P.A).left) *
        (h (x * y⁻¹).left ^ (((1 : ℕ) : ℤ) - 1) * h (x * y⁻¹ * b).left * (h b.left)⁻¹ * h (1 : Y ⟶ D.P.A).left)) =
    (h x.left ^ (((2 : ℕ) : ℤ) - 1) * h (x * (a * b)).left * (h (a * b).left)⁻¹ * h (1 : Y ⟶ D.P.A).left) *
    (h y.left ^ (((2 : ℕ) : ℤ) - 1) * h (y * c).left * (h c.left)⁻¹ * h (1 : Y ⟶ D.P.A).left) := by sorry
