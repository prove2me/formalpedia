-- Prove2me | Theorems.Thm_GlobalTheory_MulSupp_val_coord_mul
-- name    : GlobalTheory.MulSupp.val_coord_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:12:30.653292+00:00
-- url     : https://prove2.me/theorems/dd3d2d14-69d5-441b-bae5-f6f0c62324f7
-- title:
--   Mul Supp: val coord mul
-- statement:
--   The Mul Supp construction uses the val coord mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ProductSupportInSubgroupTheta.lean#L84-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ProductSupportInSubgroupTheta.lean#L84-L88

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfThickeningsOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfSumMulCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_StalkMapInjectiveOfFlat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProductSupportInSubgroupTheta
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
open GlobalTheory GlobalTheory.MulSupp
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable {D} {I : Ideal R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem GlobalTheory.MulSupp.val_coord_mul {e : ℕ} (g : GtCoord I D e G) (α β : D.X) {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e G).left)
    (z : Z) {J} (hJ : Good D.P.L z J) :
    val (g.t (α + β)) x z J * cubAt D α β (x ≫ g.pG.left) z J = val (g.t α) x z J * val (g.t β) x z J := by sorry
