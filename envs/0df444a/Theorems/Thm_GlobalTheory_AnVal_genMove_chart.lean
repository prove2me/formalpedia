-- Prove2me | Theorems.Thm_GlobalTheory_AnVal_genMove_chart
-- name    : GlobalTheory.AnVal.genMove_chart
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T04:37:19.60957+00:00
-- url     : https://prove2.me/theorems/65e9a84f-c17e-5f85-b22c-c735185c062e
-- title:
--   An Val: gen Move chart
-- statement:
--   The An Val construction uses the gen Move chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/GeneratorReadingPullbackPeriodRigid.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/GeneratorReadingPullbackPeriodRigid.lean#L31-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingPullbackPeriodRigid
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
open GlobalTheory GlobalTheory.AnVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem GlobalTheory.AnVal.genMove_chart {X Z : Scheme.{0}} (M : LB X) {K : Type} [Fintype K] (φ : K → (Z ⟶ X)) (q : Sp ℂ ⟶ Z)
    (j : K → M.ι) (h : ⊤ ≤ q ⁻¹ᵁ LB.wchart M φ j) (k : K) : ⊤ ≤ (q ≫ φ k) ⁻¹ᵁ M.U (j k) := by sorry
