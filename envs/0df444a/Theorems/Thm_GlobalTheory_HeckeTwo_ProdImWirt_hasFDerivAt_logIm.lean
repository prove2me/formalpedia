-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_ProdImWirt_hasFDerivAt_logIm
-- name    : GlobalTheory.HeckeTwo.ProdImWirt.hasFDerivAt_logIm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:06:44.659236+00:00
-- url     : https://prove2.me/theorems/3fa61209-d0ce-4dba-b0f6-6c74787bf66f
-- title:
--   Prod Im Wirt: has FDeriv At log Im
-- statement:
--   The Prod Im Wirt construction uses the has FDeriv At log Im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdImIteratedWirtingerDerivWordDifferentiableOn.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdImIteratedWirtingerDerivWordDifferentiableOn.lean#L16-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdImIteratedWirtingerDerivWordDifferentiableOn
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
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.ProdImWirt
variable {Φ : Type} [Fintype Φ]

theorem GlobalTheory.HeckeTwo.ProdImWirt.hasFDerivAt_logIm (τ : Φ) {z : Φ → ℂ} (hz : (z τ).im ≠ 0) :
    HasFDerivAt (fun z : Φ → ℂ => ((Real.log (z τ).im : ℝ) : ℂ))
      (ofRealCLM.comp (((z τ).im)⁻¹ • (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)))) z := by sorry
