-- Prove2me | Theorems.Thm_GlobalTheory_GaussHerm_finrank_V
-- name    : GlobalTheory.GaussHerm.finrank_V
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:51:11.561913+00:00
-- url     : https://prove2.me/theorems/bff822eb-94df-4ee6-9223-a36c8dacaffe
-- title:
--   Gauss Herm: finrank V
-- statement:
--   The Gauss Herm construction uses the finrank V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralExpNegHermitianFormPosDef.lean#L8-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralExpNegHermitianFormPosDef.lean#L8-L10

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralExpNegHermitianFormPosDef
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
open GlobalTheory GlobalTheory.GaussHerm

theorem GlobalTheory.GaussHerm.finrank_V (n : ℕ) : Module.finrank ℝ (V n) = 2 * n := by sorry
