-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_decay_fourier_Kc
-- name    : GroundTheory.Automorphic.LineKernel.decay_fourier_Kc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:03:37.82563+00:00
-- url     : https://prove2.me/theorems/d8d4c90d-8aff-4f75-87c6-b31331fb0e7e
-- title:
--   Line Kernel: decay fourier Kc
-- statement:
--   The Line Kernel construction uses the decay fourier Kc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L258-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L258-L274

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
variable {M : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε) {a : ℕ → ℝ} (hg : ∀ j, Good M ε j (a j))
include hε hg

theorem GroundTheory.Automorphic.LineKernel.decay_fourier_Kc (m : ℕ) : ∃ C N₀, ∀ N ≥ N₀, ∀ ξ : ℝ,
    ‖𝓕 (fun t => (Kc a (radii ε) N t : ℂ)) ξ‖ ≤ C * (1 + |ξ|) ^ (-(m : ℝ)) := by sorry
