-- Prove2me | Theorems.Thm_GroundTheory_LocalField_eq_of_eqOn_reStrip
-- name    : GroundTheory.LocalField.eq_of_eqOn_reStrip
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:25:29.496638+00:00
-- url     : https://prove2.me/theorems/f1c1e27b-5a5a-5c12-a702-804dcc44c6c9
-- title:
--   Local Field: eq of eq On re Strip
-- statement:
--   The Local Field construction uses the eq of eq On re Strip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZeta.lean#L17-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZeta.lean#L17-L28

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaGauss
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
omit [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.eq_of_eqOn_reStrip {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    {a b : ℝ} (hab : a < b) (h : ∀ s : ℂ, a < s.re → s.re < b → F s = G s) : F = G := by sorry
