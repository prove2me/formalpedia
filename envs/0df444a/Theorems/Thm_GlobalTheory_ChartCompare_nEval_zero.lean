-- Prove2me | Theorems.Thm_GlobalTheory_ChartCompare_nEval_zero
-- name    : GlobalTheory.ChartCompare.nEval_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:08:40.262812+00:00
-- url     : https://prove2.me/theorems/bf857b8d-7538-4265-8877-0d573b6960dd
-- title:
--   Chart Compare: n Eval zero
-- statement:
--   The Chart Compare construction uses the n Eval zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FiniteTorsOfFiniteTorsion.lean#L114-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FiniteTorsOfFiniteTorsion.lean#L114-L117

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_FormalChartAtZero
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_FormalGroupTorsionCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvBasicNEvalSubCoeffMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FiniteTorsOfFiniteTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing TensorProduct ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Be2 GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts
open GlobalTheory GlobalTheory.ChartCompare
variable {R₀ : Type} [CommRing R₀]
open MvPowerSeries
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S]
open IsLocalRing TensorProduct
variable {R₀ : Type} [CommRing R₀]
open MvPowerSeries
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {S : Type} [CommRing S] [Algebra R₀ S]

theorem GlobalTheory.ChartCompare.nEval_zero (a : σ → S) (ha : ∀ i, IsNilpotent (a i)) :
    _root_.ReciprocityTheory.PGsh.Be2.nEval (0 : MvPowerSeries σ R₀) a = 0 := by sorry
