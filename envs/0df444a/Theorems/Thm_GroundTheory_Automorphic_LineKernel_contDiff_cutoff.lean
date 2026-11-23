-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_contDiff_cutoff
-- name    : GroundTheory.Automorphic.LineKernel.contDiff_cutoff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:13.427786+00:00
-- url     : https://prove2.me/theorems/e7275fa7-494d-4a82-af19-77abd857ea80
-- title:
--   Line Kernel: cont Diff cutoff
-- statement:
--   The Line Kernel construction uses the cont Diff cutoff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L14-L17

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

theorem GroundTheory.Automorphic.LineKernel.contDiff_cutoff (r : ℝ) {n : ℕ∞} : ContDiff ℝ n (cutoff r) := by sorry
