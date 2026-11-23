-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_TermSmooth_norm_term_le
-- name    : GlobalTheory.HeckeTwo.TermSmooth.norm_term_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:02:08.908737+00:00
-- url     : https://prove2.me/theorems/e78c6b42-8221-4eb2-b9a0-c2a5cbdd3458
-- title:
--   Term Smooth: norm term le
-- statement:
--   The Term Smooth construction uses the norm term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContDiffOnHeckeEisensteinFourierTerm.lean#L56-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContDiffOnHeckeEisensteinFourierTerm.lean#L56-L104

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

theorem GlobalTheory.HeckeTwo.TermSmooth.norm_term_le (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) (a b m : ℕ) (hab : 2 ≤ a + 2 * b) {y₀ : ℝ}
    (hy₀ : y₀ ≠ 0) : ∃ bd : ℝ → ℝ, MeasureTheory.Integrable bd ∧
      ∀ t, ∀ y ∈ Metric.ball y₀ (|y₀| / 2), ‖term σ ν a b m y t‖ ≤ bd t := by sorry
