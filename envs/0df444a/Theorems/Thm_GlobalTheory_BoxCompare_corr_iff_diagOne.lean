-- Prove2me | Theorems.Thm_GlobalTheory_BoxCompare_corr_iff_diagOne
-- name    : GlobalTheory.BoxCompare.corr_iff_diagOne
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:01:37.900815+00:00
-- url     : https://prove2.me/theorems/7f41d31c-3562-4552-9f5e-75fc1cf78006
-- title:
--   Box Compare: corr iff diag One
-- statement:
--   The Box Compare construction uses the corr iff diag One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RestrictLineBundleSymmetryUnitsEquivIsoApply.lean#L167-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RestrictLineBundleSymmetryUnitsEquivIsoApply.lean#L167-L186

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_PowerGroupDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RestrictLineBundleSymmetryUnitsEquivIsoApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.BoxCompare
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.LB
open GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum (PowerDatum IsNormSymm)
variable {X T : Scheme.{0}} (L : LB X) (f : X ⟶ X) (e : T ⟶ X)

theorem GlobalTheory.BoxCompare.corr_iff_diagOne (he : e ≫ f = e) (sy : SymGen L f) :
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ sy e) (LB.oneGen L) ↔ DiagOne L f e sy := by sorry
