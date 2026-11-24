-- Prove2me | Theorems.Thm_GlobalTheory_BoxCompare_res_lcg_two
-- name    : GlobalTheory.BoxCompare.res_lcg_two
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:01:31.349798+00:00
-- url     : https://prove2.me/theorems/6230e0d9-7fb3-4542-ab0b-ffbb25c9be07
-- title:
--   Box Compare: res lcg two
-- statement:
--   The Box Compare construction uses the res lcg two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RestrictLineBundleSymmetryUnitsEquivIsoApply.lean#L90-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RestrictLineBundleSymmetryUnitsEquivIsoApply.lean#L90-L97

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

theorem GlobalTheory.BoxCompare.res_lcg_two (i j : Fin 2 → L.ι) {W : X.Opens}
    (h : W ≤ wchart L (K := Fin 2) ![f, 𝟙 X] i ⊓ wchart L (K := Fin 2) ![f, 𝟙 X] j)
    (h₁ : W ≤ f ⁻¹ᵁ (L.U (i 0) ⊓ L.U (j 0))) (h₂ : W ≤ L.U (i 1) ⊓ L.U (j 1)) :
    res h (lcg L (K := Fin 2) ![f, 𝟙 X] ![1, -1] i j) =
      res h₁ (pullU f _ (L.g (i 0) (j 0))) * (res h₂ (L.g (i 1) (j 1)))⁻¹ := by sorry
