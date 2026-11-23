-- Prove2me | Theorems.Thm_GlobalTheory_RawFrameBC_exists_reindexed_pull
-- name    : GlobalTheory.RawFrameBC.exists_reindexed_pull
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:23.605797+00:00
-- url     : https://prove2.me/theorems/c93b20e4-f39a-4e85-b912-37f8ca9036ef
-- title:
--   Raw Frame BC: exists reindexed pull
-- statement:
--   The Raw Frame BC construction uses the exists reindexed pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsRawChartFramesBaseChange.lean#L45-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsRawChartFramesBaseChange.lean#L45-L60

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsRawChartFramesBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.RawFrameBC

theorem GlobalTheory.RawFrameBC.exists_reindexed_pull {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φ ε)) (hc : c.IsGen) (g : Y' ⟶ Y)
    (φ' : K → (Y' ⟶ X)) (h : φ' = fun k => g ≫ φ k) :
    ∃ c' : LB.Gen (LB.LinComb L φ' ε), c'.IsGen ∧ LB.Gen.Corr L _ _ _ _ c' (LB.pullGen L φ ε c g) ∧
      ∀ (Z Z' : Scheme.{0}) (a : Z' ⟶ Y') (b : Z ⟶ Y) (r : Z' ⟶ Z), a ≫ g = r ≫ b →
        LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ' ε c' a) (LB.pullGen L _ _ (LB.pullGen L φ ε c b) r) := by sorry
