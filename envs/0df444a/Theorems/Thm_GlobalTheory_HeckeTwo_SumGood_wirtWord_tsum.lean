-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_SumGood_wirtWord_tsum
-- name    : GlobalTheory.HeckeTwo.SumGood.wirtWord_tsum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:06:41.418879+00:00
-- url     : https://prove2.me/theorems/cae6fda4-b490-4882-8b5a-670553bedd6a
-- title:
--   Sum Good: wirt Word tsum
-- statement:
--   The Sum Good construction uses the wirt Word tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoIsGoodOfTsum.lean#L127-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoIsGoodOfTsum.lean#L127-L142

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
variable {Φ : Type} [Fintype Φ] {ι : Type}

theorem GlobalTheory.HeckeTwo.SumGood.wirtWord_tsum {U : Set (Φ → ℂ)} (hU : IsOpen U) {f : ι → (Φ → ℂ) → ℂ}
    (hf : GoodFam U f) (w : List (Φ × Bool)) :
    Set.EqOn (wirtWord w (fun y => ∑' i, f i y)) (fun y => ∑' i, wirtWord w (f i) y) U := by sorry
