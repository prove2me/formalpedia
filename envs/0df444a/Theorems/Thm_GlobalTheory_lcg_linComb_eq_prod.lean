-- Prove2me | Theorems.Thm_GlobalTheory_lcg_linComb_eq_prod
-- name    : GlobalTheory.lcg_linComb_eq_prod
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:03:41.035723+00:00
-- url     : https://prove2.me/theorems/0d0516ad-78d4-44e2-99fb-71309d425427
-- title:
--   Global Theory: lcg lin Comb eq prod
-- statement:
--   The Global Theory construction uses the lcg lin Comb eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/LcgLinCombEqProd.lean#L28-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/LcgLinCombEqProd.lean#L28-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LcgLinCombEqProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.lcg_linComb_eq_prod {X X' Y : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (a b : K → (LB.LinComb L F (fun _ => 1)).ι) :
    LB.lcg (LB.LinComb L F (fun _ => 1)) φ ε a b =
      ∏ i, res (boxGen_overlap_le L F φ a b i)
        (LB.lcg (L.pull (F i)) φ ε (fun k _ => a k i) (fun k _ => b k i)) := by sorry
