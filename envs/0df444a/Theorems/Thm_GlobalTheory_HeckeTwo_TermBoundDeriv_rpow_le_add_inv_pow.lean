-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_TermBoundDeriv_rpow_le_add_inv_pow
-- name    : GlobalTheory.HeckeTwo.TermBoundDeriv.rpow_le_add_inv_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:08:18.661547+00:00
-- url     : https://prove2.me/theorems/a0a02985-7618-4fee-9c68-73f6b4dc8595
-- title:
--   Term Bound Deriv: rpow le add inv pow
-- statement:
--   The Term Bound Deriv construction uses the rpow le add inv pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedDerivHeckePhiFourierTransformBound.lean#L12-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedDerivHeckePhiFourierTransformBound.lean#L12-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivHeckePhiFourierTransformBound
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
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermBoundDeriv

theorem GlobalTheory.HeckeTwo.TermBoundDeriv.rpow_le_add_inv_pow {t r : ℝ} {s : ℕ} (ht : 0 < t) (hr : |r| ≤ s) :
    t ^ r ≤ (t + t⁻¹) ^ s := by sorry
