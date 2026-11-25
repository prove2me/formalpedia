-- Prove2me | Theorems.Thm_GlobalTheory_ThetaJet_jets_span
-- name    : GlobalTheory.ThetaJet.jets_span
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:01:06.33039+00:00
-- url     : https://prove2.me/theorems/b9f6403d-98dd-5fc9-8c9a-6812a6a8fc4b
-- title:
--   Theta Jet: jets span
-- statement:
--   The Theta Jet construction uses the jets span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsTranslateJetNeZero.lean#L257-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsTranslateJetNeZero.lean#L257-L269

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TBNFinal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelThreeSeparatesTangents
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2 Filter Topology
open GlobalTheory
open GlobalTheory.ThetaJet
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.ThetaJet.jets_span {Y : GT ι} {θ : EuclideanSpace ℂ ι → ℂ} (hθ : θ ∈ Y.Sec 1) (h0 : θ ≠ 0)
    {r : ℕ} (hr : 2 ≤ r) (D : ℕ) (x : MvPowerSeries ι ℂ) :
    ∃ s ∈ jets Y (r + 3 * D), x - s ∈ germIdeal ι ℂ ^ (D + 1) := by sorry
