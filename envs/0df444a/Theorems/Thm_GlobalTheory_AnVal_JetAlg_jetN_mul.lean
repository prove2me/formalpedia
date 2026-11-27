-- Prove2me | Theorems.Thm_GlobalTheory_AnVal_JetAlg_jetN_mul
-- name    : GlobalTheory.AnVal.JetAlg.jetN_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T04:41:20.380231+00:00
-- url     : https://prove2.me/theorems/3e4f345b-f558-4511-b09b-703e78e52869
-- title:
--   Jet Alg: jet N mul
-- statement:
--   The Jet Alg construction uses the jet N mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/JetRdMulInvPow.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/JetRdMulInvPow.lean#L24-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetRdMulInvPow
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open scoped ContDiff
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.JetAlg

theorem GlobalTheory.AnVal.JetAlg.jetN_mul {n g : ℕ} (m : ℕ) {f h : (Fin n → Fin g → ℂ) → ℂ} (hf : AnO f) (hh : AnO h) :
    jetN m (fun w => f w * h w) = jetN m f * jetN m h := by sorry
