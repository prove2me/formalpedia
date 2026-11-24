-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_ProdImWirt_hasFDerivAt_expo
-- name    : GlobalTheory.HeckeTwo.ProdImWirt.hasFDerivAt_expo
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:07:57.633629+00:00
-- url     : https://prove2.me/theorems/0ccf2d9e-b851-4847-8f60-e05acf7167ff
-- title:
--   Prod Im Wirt: has FDeriv At expo
-- statement:
--   The Prod Im Wirt construction uses the has FDeriv At expo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdImIteratedWirtingerDerivWordDifferentiableOn.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdImIteratedWirtingerDerivWordDifferentiableOn.lean#L24-L30

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

theorem GlobalTheory.HeckeTwo.ProdImWirt.hasFDerivAt_expo (A : Φ → ℂ) {z : Φ → ℂ} (hz : ∀ τ, (z τ).im ≠ 0) :
    HasFDerivAt (fun z : Φ → ℂ => ∑ τ, A τ * ((Real.log (z τ).im : ℝ) : ℂ))
      (∑ τ, A τ • (ofRealCLM.comp (((z τ).im)⁻¹ • (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ))))) z := by sorry
