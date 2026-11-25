-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv_rem_le
-- name    : GroundTheory.Automorphic.LineKernel.norm_iteratedDeriv_rem_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:28.290345+00:00
-- url     : https://prove2.me/theorems/a4cd429c-76a9-4259-bb74-ecfe3fe0a990
-- title:
--   Line Kernel: norm iterated Deriv rem le
-- statement:
--   The Line Kernel construction uses the norm iterated Deriv rem le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L389-L436
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L389-L436

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

theorem GroundTheory.Automorphic.LineKernel.norm_iteratedDeriv_rem_le {r : ℝ} (hr : 0 < r) (q : ℕ) :
    ∃ S, 0 ≤ S ∧ ∀ a, 0 ≤ a → ∀ t,
      ‖iteratedDeriv q (rem a r) t‖ ≤ 2 ^ q * (1 + a) ^ q * exp (-a * r) * S := by sorry
