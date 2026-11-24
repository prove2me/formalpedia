-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualReal_selfDual_euclid
-- name    : GlobalTheory.CompanionTheory.SelfDualReal.selfDual_euclid
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:12:29.562231+00:00
-- url     : https://prove2.me/theorems/b26727b3-75ca-4784-814d-7facd8703ed2
-- title:
--   Self Dual Real: self Dual euclid
-- statement:
--   The Self Dual Real construction uses the self Dual euclid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/BijectiveLinearCombinationOfRankAtStalk.lean#L30-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/BijectiveLinearCombinationOfRankAtStalk.lean#L30-L78

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped FourierTransform RealInnerProductSpace
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SelfDualReal

theorem GlobalTheory.CompanionTheory.SelfDualReal.selfDual_euclid {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] (S : W →ₗ[ℝ] W)
    (hS : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫) (hd : LinearMap.det S ≠ 0) :
    ∃ ν : Measure W, SelfDual ν
      (fun x y => Complex.exp (((-2 * Real.pi * ⟪x, S y⟫ : ℝ) : ℂ) * Complex.I)) := by sorry
