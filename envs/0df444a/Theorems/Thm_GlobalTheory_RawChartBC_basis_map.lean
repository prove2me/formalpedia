-- Prove2me | Theorems.Thm_GlobalTheory_RawChartBC_basis_map
-- name    : GlobalTheory.RawChartBC.basis_map
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:15:05.446258+00:00
-- url     : https://prove2.me/theorems/7d22e927-9101-4113-8983-028d4816b756
-- title:
--   Raw Chart BC: basis map
-- statement:
--   The Raw Chart BC construction uses the basis map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsRawChartBaseChangeJetPoints.lean#L41-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsRawChartBaseChangeJetPoints.lean#L41-L72

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsRawChartBaseChangeJetPoints
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
open GlobalTheory GlobalTheory.RawChartBC
open ReciprocityTheory.ChartRestriction.G.PullbackSections

theorem GlobalTheory.RawChartBC.basis_map {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') {σ κ : Type} [Fintype σ] [Fintype κ]
    (U : σ → κ → S) (h : ∀ v : κ → S, ∃! a : σ → S, ∀ j, ∑ ℓ, a ℓ * U ℓ j = v j) (v : κ → S') :
    ∃! a : σ → S', ∀ j, ∑ ℓ, a ℓ * ψ (U ℓ j) = v j := by sorry
