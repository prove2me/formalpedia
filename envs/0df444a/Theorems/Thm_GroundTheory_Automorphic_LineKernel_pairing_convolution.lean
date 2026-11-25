-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_pairing_convolution
-- name    : GroundTheory.Automorphic.LineKernel.pairing_convolution
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:31:50.225402+00:00
-- url     : https://prove2.me/theorems/e574068a-8cbd-47dc-88b2-cea50d086f8a
-- title:
--   Line Kernel: pairing convolution
-- statement:
--   The Line Kernel construction uses the pairing convolution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L46-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L46-L80

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
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
open scoped ContDiff Convolution Pointwise
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel

theorem GroundTheory.Automorphic.LineKernel.pairing_convolution {G K k : ℝ → ℂ} (hG : Continuous G) (hK : Integrable K)
    (hk : Integrable k) (hKc : HasCompactSupport K) (hkc : HasCompactSupport k) :
    Integrable (fun s => K s * ∫ t, G (s + t) * k t) ∧
      ∫ u, G u * (K ⋆[mul ℂ ℂ] k) u = ∫ s, K s * ∫ t, G (s + t) * k t := by sorry
