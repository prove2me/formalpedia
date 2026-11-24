-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_ProdImWirt_hasFDerivAt_mono
-- name    : GlobalTheory.HeckeTwo.ProdImWirt.hasFDerivAt_mono
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:06:34.624799+00:00
-- url     : https://prove2.me/theorems/990b1f6d-0e36-4ac0-9c79-d419fc588025
-- title:
--   Prod Im Wirt: has FDeriv At mono
-- statement:
--   The Prod Im Wirt construction uses the has FDeriv At mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdImIteratedWirtingerDerivWordDifferentiableOn.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdImIteratedWirtingerDerivWordDifferentiableOn.lean#L32-L35

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

theorem GlobalTheory.HeckeTwo.ProdImWirt.hasFDerivAt_mono (c : ℂ → ℂ) (a : ℂ → Φ → ℂ) (σ : ℂ) {z : Φ → ℂ} (hz : ∀ τ, (z τ).im ≠ 0) :
    HasFDerivAt (mono c a σ)
      (c σ • (Complex.exp (∑ τ, a σ τ * ((Real.log (z τ).im : ℝ) : ℂ)) • ∑ τ, a σ τ • (ofRealCLM.comp (((z τ).im)⁻¹ • (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)))))) z := by sorry
