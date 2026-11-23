-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_SumGood_wirt_eq_clm
-- name    : GlobalTheory.HeckeTwo.SumGood.wirt_eq_clm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:02:07.901054+00:00
-- url     : https://prove2.me/theorems/e5514eeb-769f-4bc7-8a9e-fed71bb7d968
-- title:
--   Sum Good: wirt eq clm
-- statement:
--   The Sum Good construction uses the wirt eq clm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoIsGoodOfTsum.lean#L76-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoIsGoodOfTsum.lean#L76-L87

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

theorem GlobalTheory.HeckeTwo.SumGood.wirt_eq_clm (τ : Φ) (b : Bool) :
    ∃ Λ : ((Φ → ℂ) →L[ℝ] ℂ) →L[ℝ] ℂ, ∀ (h : (Φ → ℂ) → ℂ) (z : Φ → ℂ),
      wirt τ b h z = Λ (fderiv ℝ h z) := by sorry
