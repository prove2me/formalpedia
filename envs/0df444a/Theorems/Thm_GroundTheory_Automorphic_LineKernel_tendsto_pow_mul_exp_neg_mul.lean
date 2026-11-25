-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_tendsto_pow_mul_exp_neg_mul
-- name    : GroundTheory.Automorphic.LineKernel.tendsto_pow_mul_exp_neg_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:32:00.786445+00:00
-- url     : https://prove2.me/theorems/12cce88d-f8a4-4dca-a73e-18d7334b7bcc
-- title:
--   Line Kernel: tendsto pow mul exp neg mul
-- statement:
--   The Line Kernel construction uses the tendsto pow mul exp neg mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L438-L447
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L438-L447

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function
open scoped ContDiff FourierTransform
noncomputable section
open GroundTheory.Automorphic.LineKernel

theorem GroundTheory.Automorphic.LineKernel.tendsto_pow_mul_exp_neg_mul {r : ℝ} (hr : 0 < r) (q : ℕ) :
    Tendsto (fun a : ℝ => (1 + a) ^ q * exp (-a * r)) atTop (𝓝 0) := by sorry
