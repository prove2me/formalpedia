-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_TermSmooth_contDiffOn_intT
-- name    : GlobalTheory.HeckeTwo.TermSmooth.contDiffOn_intT
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:06:58.598321+00:00
-- url     : https://prove2.me/theorems/d4b0c09c-7a13-439d-a909-b7586dbf29c8
-- title:
--   Term Smooth: cont Diff On int T
-- statement:
--   The Term Smooth construction uses the cont Diff On int T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContDiffOnHeckeEisensteinFourierTerm.lean#L160-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContDiffOnHeckeEisensteinFourierTerm.lean#L160-L175

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

theorem GlobalTheory.HeckeTwo.TermSmooth.contDiffOn_intT (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) :
    ∀ n : ℕ, ∀ a b m : ℕ, 2 ≤ a + 2 * b → ContDiffOn ℝ n (intT σ ν a b m) {y | y ≠ 0} := by sorry
