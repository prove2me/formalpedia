-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwoEq_fTerm_zero
-- name    : GlobalTheory.HeckeTwoEq.fTerm_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:16:17.883893+00:00
-- url     : https://prove2.me/theorems/835ad7ec-6527-4f70-80cd-408ef8796e83
-- title:
--   Hecke Two Eq: f Term zero
-- statement:
--   The Hecke Two Eq construction uses the f Term zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoContinuationEqLatticeSeries.lean#L66-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoContinuationEqLatticeSeries.lean#L66-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHilbertEisensteinLatticeClassWeightTwoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumLatticePairUnitQuotientRegroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoPoissonSummationFractionalIdealStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformZeroEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumAbsNormCpowUnitClassesPartialZetaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoContinuationEqLatticeSeries
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
open GlobalTheory GlobalTheory.HeckeTwoEq
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.HeckeTwoEq.fTerm_zero [IsTotallyReal F] (hzero : ∀ (σ : ℂ) (y : ℝ), y ≠ 0 → GlobalTheory.HeckeTwo.hTrans σ 0 y = GlobalTheory.HeckeTwo.cConst σ * ((|y| : ℝ) : ℂ) ^ (-1 - 2 * σ)) (σ : ℂ) {z : Emb F → ℂ} (hz : z ∈ upperHalf F) {b : F} (hb : b ≠ 0) :
    fTerm σ z b 0 = (∏ τ : Emb F, (cConst σ * (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ))) *
      ((|((Algebra.norm ℚ b : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-1 - 2 * σ) := by sorry
