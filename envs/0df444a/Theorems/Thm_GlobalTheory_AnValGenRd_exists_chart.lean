-- Prove2me | Theorems.Thm_GlobalTheory_AnValGenRd_exists_chart
-- name    : GlobalTheory.AnValGenRd.exists_chart
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T04:35:52.01383+00:00
-- url     : https://prove2.me/theorems/8fc04a13-2792-5ab1-8948-240e8351a642
-- title:
--   An Val Gen Rd: exists chart
-- statement:
--   The An Val Gen Rd construction uses the exists chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsHolomorphicGeneratorReadingAutomorphy.lean#L115-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsHolomorphicGeneratorReadingAutomorphy.lean#L115-L125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsHolomorphicGeneratorReadingAutomorphy
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_exists_chart

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
open GlobalTheory GlobalTheory.AnValGenRd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open ReciprocityTheory.ChartRestriction.G.TB.ValAt
attribute [local instance] Over.cartesianMonoidalCategory
variable {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]

theorem GlobalTheory.AnValGenRd.exists_chart (hL : L.IsLB) (φ : K → (Y ⟶ X)) (x : Sp ℂ ⟶ Y) :
    ∃ j : K → L.ι, ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j := by sorry
