-- Prove2me | Theorems.Thm_GlobalTheory_GaussExpSeries_norm_iteratedFDeriv_cexp
-- name    : GlobalTheory.GaussExpSeries.norm_iteratedFDeriv_cexp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:51:05.868735+00:00
-- url     : https://prove2.me/theorems/bd81f5e1-deba-4d07-8db9-712414d8e5e0
-- title:
--   Gauss Exp Series: norm iterated FDeriv cexp
-- statement:
--   The Gauss Exp Series construction uses the norm iterated FDeriv cexp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivTruncExpICompLe.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivTruncExpICompLe.lean#L16-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzContinuousAtOfPointwiseOfBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolyMulGaussianBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivTruncExpICompLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped Nat
noncomputable section
open GlobalTheory GlobalTheory.GaussExpSeries
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem GlobalTheory.GaussExpSeries.norm_iteratedFDeriv_cexp (i : ℕ) (z : ℂ) : ‖iteratedFDeriv ℝ i Complex.exp z‖ = Real.exp z.re := by sorry
