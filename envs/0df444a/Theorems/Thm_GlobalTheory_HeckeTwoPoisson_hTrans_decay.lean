-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwoPoisson_hTrans_decay
-- name    : GlobalTheory.HeckeTwoPoisson.hTrans_decay
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:10:53.019865+00:00
-- url     : https://prove2.me/theorems/e6c21f7e-4468-4174-8fca-84325376b526
-- title:
--   Hecke Two Poisson: h Trans decay
-- statement:
--   The Hecke Two Poisson construction uses the h Trans decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoPoissonSummationFractionalIdeal.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoPoissonSummationFractionalIdeal.lean#L25-L26

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

theorem GlobalTheory.HeckeTwoPoisson.hTrans_decay : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 → ∀ (N : ℕ), ∃ C : ℝ, ∀ ν : ℝ,
    ‖GlobalTheory.HeckeTwo.hTrans σ ν y‖ ≤ C * (1 + |ν|) ^ (-(N : ℝ)) := by sorry
