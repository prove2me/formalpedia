-- Prove2me | Theorems.Thm_GlobalTheory_TruncGauss_isCompact_bdd
-- name    : GlobalTheory.TruncGauss.isCompact_bdd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:59:30.120964+00:00
-- url     : https://prove2.me/theorems/fa0bf996-6136-463c-b0fc-3fdf050abec2
-- title:
--   Trunc Gauss: is Compact bdd
-- statement:
--   The Trunc Gauss construction uses the is Compact bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedGaussianIntegralUniformPosSemidef.lean#L37-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedGaussianIntegralUniformPosSemidef.lean#L37-L48

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralExpNegHermitianFormPosDefStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedGaussianIntegralUniformPosSemidef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
open GlobalTheory GlobalTheory.TruncGauss

theorem GlobalTheory.TruncGauss.isCompact_bdd (n : ℕ) (C : ℝ) :
    IsCompact {H : Matrix (Fin n) (Fin n) ℂ | ∀ j l, ‖H j l‖ ≤ C} := by sorry
