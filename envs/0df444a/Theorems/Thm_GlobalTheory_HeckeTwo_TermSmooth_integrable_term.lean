-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_TermSmooth_integrable_term
-- name    : GlobalTheory.HeckeTwo.TermSmooth.integrable_term
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:07:58.021206+00:00
-- url     : https://prove2.me/theorems/2a5a59cd-31f9-4ad4-9bf8-a435719913f7
-- title:
--   Term Smooth: integrable term
-- statement:
--   The Term Smooth construction uses the integrable term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContDiffOnHeckeEisensteinFourierTerm.lean#L112-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContDiffOnHeckeEisensteinFourierTerm.lean#L112-L116

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

theorem GlobalTheory.HeckeTwo.TermSmooth.integrable_term (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) {a b : ℕ} (m : ℕ) (hab : 2 ≤ a + 2 * b) {y : ℝ}
    (hy : y ≠ 0) : MeasureTheory.Integrable (term σ ν a b m y) := by sorry
