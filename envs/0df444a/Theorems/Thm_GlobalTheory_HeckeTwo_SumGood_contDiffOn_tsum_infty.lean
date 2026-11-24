-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_SumGood_contDiffOn_tsum_infty
-- name    : GlobalTheory.HeckeTwo.SumGood.contDiffOn_tsum_infty
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:06:53.462328+00:00
-- url     : https://prove2.me/theorems/c08a8c7d-e2ea-494e-a2a7-27a760664ffa
-- title:
--   Sum Good: cont Diff On tsum infty
-- statement:
--   The Sum Good construction uses the cont Diff On tsum infty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoIsGoodOfTsum.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoIsGoodOfTsum.lean#L65-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoIsGoodOfTsum
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
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.SumGood
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V] {ι : Type}

theorem GlobalTheory.HeckeTwo.SumGood.contDiffOn_tsum_infty {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set V} (hU : IsOpen U) {f : ι → V → E} (hf : GoodFam U f) :
    ContDiffOn ℝ ∞ (fun y => ∑' i, f i y) U := by sorry
