-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwoPoisson_hTrans_eq_fourier
-- name    : GlobalTheory.HeckeTwoPoisson.hTrans_eq_fourier
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:08:11.625514+00:00
-- url     : https://prove2.me/theorems/1dc2b6dc-715f-410b-9d92-d3c409a25472
-- title:
--   Hecke Two Poisson: h Trans eq fourier
-- statement:
--   The Hecke Two Poisson construction uses the h Trans eq fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoPoissonSummationFractionalIdeal.lean#L61-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoPoissonSummationFractionalIdeal.lean#L61-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiscreteTopologyFractionalIdealRealLatticeImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsZLatticeFractionalIdealRealLatticeImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovolumeFractionalIdealRealLatticeImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualLatticeImageEqLatticeImageTraceDual
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformRapidDecayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoKernelPhiLineContinuousIntegrableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHeckeWeightTwoLatticeSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdRpowDecayIsBigOCocompactStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoPoissonSummationFractionalIdeal
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_hTrans_eq_fourier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex MeasureTheory
open scoped nonZeroDivisors ContDiff FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoPoisson
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.LipschitzTR

theorem GlobalTheory.HeckeTwoPoisson.hTrans_eq_fourier (σ : ℂ) (y : ℝ) :
    (fun ν : ℝ => hTrans σ ν y) = 𝓕 (fun t : ℝ => phi σ ((t : ℂ) + (y : ℂ) * I)) := by sorry
