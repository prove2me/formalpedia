-- Prove2me | Theorems.Thm_GlobalTheory_BoxCompare_isNormSymm_iff
-- name    : GlobalTheory.BoxCompare.isNormSymm_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:01:31.890819+00:00
-- url     : https://prove2.me/theorems/ed13db34-ee63-44c0-a24d-3403b9d22d34
-- title:
--   Box Compare: is Norm Symm iff
-- statement:
--   The Box Compare construction uses the is Norm Symm iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RestrictLineBundleSymmetryUnitsEquivIsoApply.lean#L268-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RestrictLineBundleSymmetryUnitsEquivIsoApply.lean#L268-L273

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
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem GlobalTheory.BoxCompare.isNormSymm_iff (L : RigLB G) (sy : SymGen L.L (ι[G]).left) :
    IsNormSymm L (symEquiv L.L _ sy) ↔ IsCanonSym L.L sy := by sorry
