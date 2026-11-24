-- Prove2me | Theorems.Thm_GlobalTheory_GaussExpSeries_norm_iteratedFDeriv_gauss_le
-- name    : GlobalTheory.GaussExpSeries.norm_iteratedFDeriv_gauss_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:50:33.411356+00:00
-- url     : https://prove2.me/theorems/b7f8f40f-d964-4fe9-9fcd-0c173d986759
-- title:
--   Gauss Exp Series: norm iterated FDeriv gauss le
-- statement:
--   The Gauss Exp Series construction uses the norm iterated FDeriv gauss le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivTruncExpICompLe.lean#L57-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivTruncExpICompLe.lean#L57-L73

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

theorem GlobalTheory.GaussExpSeries.norm_iteratedFDeriv_gauss_le (B : V →L[ℝ] V →L[ℝ] ℂ) (ε : ℝ)
    (hB : ∀ x, (B x x).re ≤ -(ε * ‖x‖ ^ 2)) (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun y => Complex.exp (B y y)) x‖ ≤
      n ! * Real.exp (-(ε * ‖x‖ ^ 2)) * (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ n := by sorry
