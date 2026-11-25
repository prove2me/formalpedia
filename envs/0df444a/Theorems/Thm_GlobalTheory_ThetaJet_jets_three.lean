-- Prove2me | Theorems.Thm_GlobalTheory_ThetaJet_jets_three
-- name    : GlobalTheory.ThetaJet.jets_three
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:01:51.411804+00:00
-- url     : https://prove2.me/theorems/550190e4-85ba-4190-978e-93c7f9297e48
-- title:
--   Theta Jet: jets three
-- statement:
--   The Theta Jet construction uses the jets three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsTranslateJetNeZero.lean#L212-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsTranslateJetNeZero.lean#L212-L255

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

theorem GlobalTheory.ThetaJet.jets_three {Y : GT ι} {θ : EuclideanSpace ℂ ι → ℂ} (hθ : θ ∈ Y.Sec 1) (h0 : θ ≠ 0)
    (x : MvPowerSeries ι ℂ) : ∃ s ∈ jets Y 3, x - s ∈ germIdeal ι ℂ ^ 2 := by sorry
