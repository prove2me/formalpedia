-- Prove2me | Theorems.Thm_GlobalTheory_UU_BoxSec_prod_famT
-- name    : GlobalTheory.UU.BoxSec.prod_famT
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:35:12.777738+00:00
-- url     : https://prove2.me/theorems/2d5d2c22-c86e-42d0-a204-bd8df94c31c3
-- title:
--   Box Sec: prod fam T
-- statement:
--   The Box Sec construction uses the prod fam T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RepSymInv.lean#L108-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RepSymInv.lean#L108-L120

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

theorem GlobalTheory.UU.BoxSec.prod_famT {T T₀ : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ T₀) (x : T ⟶ D.P.A) (α : D.X) (k : ℕ) {U : Type}
    [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) : ∏ i, h ((lift ρ x).left ≫ famφT D T₀ α i) ^ DegPre.famε k i =
      h x.left ^ ((k : ℤ) - 1) * h (x * cT D T α).left * (h (cT D T α).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by sorry
