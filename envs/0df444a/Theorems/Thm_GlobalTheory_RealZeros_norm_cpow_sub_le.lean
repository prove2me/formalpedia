-- Prove2me | Theorems.Thm_GlobalTheory_RealZeros_norm_cpow_sub_le
-- name    : GlobalTheory.RealZeros.norm_cpow_sub_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:18:15.71416+00:00
-- url     : https://prove2.me/theorems/3c258337-b1c3-405b-b6b1-55f62fdafa92
-- title:
--   Real Zeros: norm cpow sub le
-- statement:
--   The Real Zeros construction uses the norm cpow sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean#L7-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean#L7-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannZetaNeZeroOfMemIoo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
open GlobalTheory GlobalTheory.RealZeros

theorem GlobalTheory.RealZeros.norm_cpow_sub_le {s : ℂ} (hs : 0 < s.re) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ‖(a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)‖ ≤ ‖s‖ * a ^ (-s.re - 1) * (b - a) := by sorry
