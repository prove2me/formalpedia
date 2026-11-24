-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_TermDecay_term_eq_qZ
-- name    : GlobalTheory.HeckeTwo.TermDecay.term_eq_qZ
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:07:10.775252+00:00
-- url     : https://prove2.me/theorems/3ddc413e-e7cd-436d-87b5-0b792d694cdf
-- title:
--   Term Decay: term eq q Z
-- statement:
--   The Term Decay construction uses the term eq q Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntZEqFourier.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntZEqFourier.lean#L19-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntZEqFourier
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
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay

theorem GlobalTheory.HeckeTwo.TermDecay.term_eq_qZ (σ : ℂ) (ν : ℝ) (a b m : ℕ) (y t : ℝ) :
    GlobalTheory.HeckeTwo.TermSmooth.term σ ν a b m y t =
      qZ σ (a : ℤ) b m y t * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))) := by sorry
