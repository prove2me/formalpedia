-- Prove2me | Theorems.Thm_GlobalTheory_RealZeros_differentiableOn_tsum_br
-- name    : GlobalTheory.RealZeros.differentiableOn_tsum_br
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:16:46.702828+00:00
-- url     : https://prove2.me/theorems/90a64091-a1a3-4543-8b52-1cb742ae9862
-- title:
--   Real Zeros: differentiable On tsum br
-- statement:
--   The Real Zeros construction uses the differentiable On tsum br property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean#L65-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean#L65-L81

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

theorem GlobalTheory.RealZeros.differentiableOn_tsum_br {N c d : ℕ} (hN : 1 ≤ N) (hc : 1 ≤ c) (hcd : c ≤ d) :
    DifferentiableOn ℂ (fun s => ∑' k, br N c d k s) {s | 0 < s.re} := by sorry
