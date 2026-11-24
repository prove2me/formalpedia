-- Prove2me | Theorems.Thm_GlobalTheory_BoxCompare_res_dg_pull
-- name    : GlobalTheory.BoxCompare.res_dg_pull
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:01:10.531205+00:00
-- url     : https://prove2.me/theorems/2ee16989-b752-498f-98d4-4c38567f5d96
-- title:
--   Box Compare: res dg pull
-- statement:
--   The Box Compare construction uses the res dg pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RestrictLineBundleSymmetryUnitsEquivIsoApply.lean#L99-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RestrictLineBundleSymmetryUnitsEquivIsoApply.lean#L99-L106

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

theorem GlobalTheory.BoxCompare.res_dg_pull (p q : (PUnit.{1} → L.ι) × L.ι) {W : X.Opens}
    (h : W ≤ wchart L (fun _ : PUnit.{1} => f) p.1 ⊓ L.U p.2 ⊓
      (wchart L (fun _ : PUnit.{1} => f) q.1 ⊓ L.U q.2))
    (h₁ : W ≤ f ⁻¹ᵁ (L.U (p.1 ⟨⟩) ⊓ L.U (q.1 ⟨⟩))) (h₂ : W ≤ L.U p.2 ⊓ L.U q.2) :
    res h (dg (L.pull f) L p q) =
      res h₁ (pullU f _ (L.g (p.1 ⟨⟩) (q.1 ⟨⟩))) * (res h₂ (L.g p.2 q.2))⁻¹ := by sorry
