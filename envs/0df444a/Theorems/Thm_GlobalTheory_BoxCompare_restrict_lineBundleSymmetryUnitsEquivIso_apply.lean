-- Prove2me | Theorems.Thm_GlobalTheory_BoxCompare_restrict_lineBundleSymmetryUnitsEquivIso_apply
-- name    : GlobalTheory.BoxCompare.restrict_lineBundleSymmetryUnitsEquivIso_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:01:44.785256+00:00
-- url     : https://prove2.me/theorems/fa35a0ff-3c22-43b1-812b-60e970926ea8
-- title:
--   Box Compare: restrict line Bundle Symmetry Units Equiv Iso apply
-- statement:
--   The Box Compare construction uses the restrict line Bundle Symmetry Units Equiv Iso apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RestrictLineBundleSymmetryUnitsEquivIsoApply.lean#L84-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RestrictLineBundleSymmetryUnitsEquivIsoApply.lean#L84-L88

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
variable {X T : Scheme.{0}} (L : LB X) (f : X ⟶ X)

theorem GlobalTheory.BoxCompare.restrict_lineBundleSymmetryUnitsEquivIso_apply (sy : SymGen L f) (p : (PUnit.{1} → L.ι) × L.ι) {W : X.Opens}
    (h : W ≤ wchart L (fun _ : PUnit.{1} => f) p.1 ⊓ L.U p.2)
    (h' : W ≤ wchart L (K := Fin 2) ![f, 𝟙 X] ![p.1 ⟨⟩, p.2]) :
    res h ((symEquiv L f sy).s p) = res h' (ts sy ![p.1 ⟨⟩, p.2]) := by sorry
