-- Prove2me | Theorems.Thm_GlobalTheory_TorsionIntegral_exists_gen_of_chart
-- name    : GlobalTheory.TorsionIntegral.exists_gen_of_chart
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T16:29:00.927288+00:00
-- url     : https://prove2.me/theorems/36e9140c-0b36-4b62-b198-b75fd0307d43
-- title:
--   Torsion Integral: exists gen of chart
-- statement:
--   The Torsion Integral construction uses the exists gen of chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorsionPointsIntegral.lean#L144-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorsionPointsIntegral.lean#L144-L159

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorsionPointsIntegral
import Theorems.Thm_GlobalTheory_WeilCube_exists_gen_of_chart
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019

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
open GlobalTheory
open GlobalTheory.TorsionIntegral
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem GlobalTheory.TorsionIntegral.exists_gen_of_chart (hL : L.IsLB) (ψ : K → (Y ⟶ X)) (ε : K → ℤ) (j₀ : K → L.ι)
    (h₀ : ∀ y, y ∈ LB.wchart L ψ j₀) (u : Γ(Y, ⊤)ˣ) :
    ∃ t : LB.Gen (LB.LinComb L ψ ε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι),
      r z ∈ LB.wchart L ψ j → gm r z (LB.wchart L ψ j) (t.s j) = trF ψ ε r z j j₀ * gm r z ⊤ u := by sorry
