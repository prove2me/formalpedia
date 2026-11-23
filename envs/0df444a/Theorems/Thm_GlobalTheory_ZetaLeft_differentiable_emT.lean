-- Prove2me | Theorems.Thm_GlobalTheory_ZetaLeft_differentiable_emT
-- name    : GlobalTheory.ZetaLeft.differentiable_emT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:17.941666+00:00
-- url     : https://prove2.me/theorems/92dd820a-145e-44eb-a54a-e7e193c8bf64
-- title:
--   Zeta Left: differentiable em T
-- statement:
--   The Zeta Left construction uses the differentiable em T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormSubOneMulRiemannZetaLe.lean#L96-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormSubOneMulRiemannZetaLe.lean#L96-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open GlobalTheory GlobalTheory.ZetaLeft

theorem GlobalTheory.ZetaLeft.differentiable_emT {x : ℝ} (hx : 0 < x) : Differentiable ℂ (emT x) := by sorry
