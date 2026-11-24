-- Prove2me | Theorems.Thm_GlobalTheory_PerronPsi_harm
-- name    : GlobalTheory.PerronPsi.harm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:43:28.195397+00:00
-- url     : https://prove2.me/theorems/72d96f2d-4ea1-4943-a9c4-f69b9c8bbbf1
-- title:
--   Perron Psi: harm
-- statement:
--   The Perron Psi construction uses the harm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronPsi.lean#L217-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronPsi.lean#L217-L221

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronPsi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PerronPsi

theorem GlobalTheory.PerronPsi.harm (N : ℕ) : ∑ k ∈ Finset.range (N + 1), 1 / (k : ℝ) ≤ 1 + Real.log N := by sorry
