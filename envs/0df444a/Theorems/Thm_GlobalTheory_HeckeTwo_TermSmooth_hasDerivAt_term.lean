-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_TermSmooth_hasDerivAt_term
-- name    : GlobalTheory.HeckeTwo.TermSmooth.hasDerivAt_term
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:06:54.647486+00:00
-- url     : https://prove2.me/theorems/63927765-f228-4e2a-bb6b-90ba6384c2e9
-- title:
--   Term Smooth: has Deriv At term
-- statement:
--   The Term Smooth construction uses the has Deriv At term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContDiffOnHeckeEisensteinFourierTerm.lean#L19-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContDiffOnHeckeEisensteinFourierTerm.lean#L19-L45

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

theorem GlobalTheory.HeckeTwo.TermSmooth.hasDerivAt_term (σ : ℂ) (ν : ℝ) (a b m : ℕ) {y : ℝ} (hy : y ≠ 0) (t : ℝ) :
    HasDerivAt (fun y => term σ ν a b m y t)
      (-(a : ℂ) * I * term σ ν (a + 1) b m y t + 2 * (-σ - (b : ℂ)) * term σ ν a (b + 1) (m + 1) y t
        + (m : ℂ) * term σ ν a b (m - 1) y t) y := by sorry
