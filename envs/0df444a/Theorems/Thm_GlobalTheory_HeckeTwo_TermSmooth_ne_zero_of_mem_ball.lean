-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_TermSmooth_ne_zero_of_mem_ball
-- name    : GlobalTheory.HeckeTwo.TermSmooth.ne_zero_of_mem_ball
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:07:12.530156+00:00
-- url     : https://prove2.me/theorems/4d495af9-6c39-4d16-8d38-5f44c5d4e9f3
-- title:
--   Term Smooth: ne zero of mem ball
-- statement:
--   The Term Smooth construction uses the ne zero of mem ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContDiffOnHeckeEisensteinFourierTerm.lean#L106-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContDiffOnHeckeEisensteinFourierTerm.lean#L106-L110

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermSmooth

theorem GlobalTheory.HeckeTwo.TermSmooth.ne_zero_of_mem_ball {y₀ y : ℝ} (hy₀ : y₀ ≠ 0) (hy : y ∈ Metric.ball y₀ (|y₀| / 2)) : y ≠ 0 := by sorry
