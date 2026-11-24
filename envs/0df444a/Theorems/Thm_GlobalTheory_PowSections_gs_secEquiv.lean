-- Prove2me | Theorems.Thm_GlobalTheory_PowSections_gs_secEquiv
-- name    : GlobalTheory.PowSections.gs_secEquiv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:55:51.229194+00:00
-- url     : https://prove2.me/theorems/bae2fbfd-f56b-444a-9f1b-7cc461b1ce09
-- title:
--   Pow Sections: gs sec Equiv
-- statement:
--   The Pow Sections construction uses the gs sec Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsEquivPow.lean#L62-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsEquivPow.lean#L62-L67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsEquivPow
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
noncomputable section
open GlobalTheory
open GlobalTheory.PowSections
variable {Y : Scheme.{0}}

theorem GlobalTheory.PowSections.gs_secEquiv {M M' : LB Y} (σ : M'.ι ≃ M.ι) (hU : ∀ i, M'.U i = M.U (σ i))
    (hg : ∀ i j y, y ∈ M'.U i → y ∈ M'.U j →
      gm (𝟙 Y) y _ (M'.g i j) = gm (𝟙 Y) y _ (M.g (σ i) (σ j))) (s : LB.Sec M) (i : M'.ι) (y : Y)
    (hy : y ∈ M'.U i) :
    gs (𝟙 Y) y _ ((secEquiv σ hU hg s).f i) = gs (𝟙 Y) y _ (s.f (σ i)) := by sorry
