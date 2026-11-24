-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_SumGood_wirtWord_congr
-- name    : GlobalTheory.HeckeTwo.SumGood.wirtWord_congr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:07:02.268941+00:00
-- url     : https://prove2.me/theorems/fd72ea9f-56fa-4b93-810a-f3f82064fc58
-- title:
--   Sum Good: wirt Word congr
-- statement:
--   The Sum Good construction uses the wirt Word congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoIsGoodOfTsum.lean#L89-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoIsGoodOfTsum.lean#L89-L93

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

theorem GlobalTheory.HeckeTwo.SumGood.wirtWord_congr {U : Set (Φ → ℂ)} (hU : IsOpen U) (w : List (Φ × Bool))
    {f g : (Φ → ℂ) → ℂ} (h : Set.EqOn f g U) : Set.EqOn (wirtWord w f) (wirtWord w g) U := by sorry
