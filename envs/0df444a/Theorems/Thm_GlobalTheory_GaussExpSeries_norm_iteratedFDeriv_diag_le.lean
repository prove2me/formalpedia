-- Prove2me | Theorems.Thm_GlobalTheory_GaussExpSeries_norm_iteratedFDeriv_diag_le
-- name    : GlobalTheory.GaussExpSeries.norm_iteratedFDeriv_diag_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:51:41.844815+00:00
-- url     : https://prove2.me/theorems/b214ff80-26a5-488e-abc9-94856af7d396
-- title:
--   Gauss Exp Series: norm iterated FDeriv diag le
-- statement:
--   The Gauss Exp Series construction uses the norm iterated FDeriv diag le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivTruncExpICompLe.lean#L38-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivTruncExpICompLe.lean#L38-L55

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

theorem GlobalTheory.GaussExpSeries.norm_iteratedFDeriv_diag_le (B : V →L[ℝ] V →L[ℝ] ℂ) (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun y => B y y) x‖ ≤ ‖B‖ * (2 ^ n * (1 + ‖x‖) ^ 2) := by sorry
