-- Prove2me | Theorems.Thm_GlobalTheory_RootNormPowerBound_exists_root_norm_sub_pow_le
-- name    : GlobalTheory.RootNormPowerBound.exists_root_norm_sub_pow_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:30:38.315444+00:00
-- url     : https://prove2.me/theorems/61695682-2bf7-4ac4-8888-bab56de7d12a
-- title:
--   Root Norm Power Bound: exists root norm sub pow le
-- statement:
--   The Root Norm Power Bound construction uses the exists root norm sub pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsRootNormSubPowLe.lean#L22-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsRootNormSubPowLe.lean#L22-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRootNormSubPowLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.RootNormPowerBound
open Polynomial

theorem GlobalTheory.RootNormPowerBound.exists_root_norm_sub_pow_le {K : Type u_1} [inst : NormedField K] [IsAlgClosed K]
    (p : Polynomial K) (hp : (0 : ℕ) < Polynomial.natDegree p) (x : K) :
    ∃ b ∈ Polynomial.roots p,
      ‖Polynomial.leadingCoeff p‖ * ‖b - x‖ ^ Polynomial.natDegree p ≤ ‖Polynomial.eval x p‖ := by sorry
