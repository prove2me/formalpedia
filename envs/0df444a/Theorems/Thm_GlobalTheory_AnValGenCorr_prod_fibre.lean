-- Prove2me | Theorems.Thm_GlobalTheory_AnValGenCorr_prod_fibre
-- name    : GlobalTheory.AnValGenCorr.prod_fibre
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T04:39:27.012453+00:00
-- url     : https://prove2.me/theorems/2131b342-15e9-457a-93ea-63570000d14f
-- title:
--   An Val Gen Corr: prod fibre
-- statement:
--   The An Val Gen Corr construction uses the prod fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/GeneratorReadingCorrMulInv.lean#L53-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/GeneratorReadingCorrMulInv.lean#L53-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingCorrMulInv
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
open GlobalTheory GlobalTheory.AnValGenCorr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open scoped Classical

theorem GlobalTheory.AnValGenCorr.prod_fibre {T K : Type} [Fintype K] (φ : K → T) (ε : K → ℤ) (f : T → ℂ) (s : Finset T)
    (hs : ∀ k, φ k ∈ s) (hf : ∀ ψ ∈ s, f ψ ≠ 0) :
    ∏ k, f (φ k) ^ ε k = ∏ ψ ∈ s, f ψ ^ (∑ k, if φ k = ψ then ε k else 0) := by sorry
