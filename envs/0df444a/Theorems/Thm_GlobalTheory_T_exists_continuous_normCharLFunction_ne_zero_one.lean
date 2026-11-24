-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_continuous_normCharLFunction_ne_zero_one
-- name    : GlobalTheory.T.exists_continuous_normCharLFunction_ne_zero_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:35:08.871368+00:00
-- url     : https://prove2.me/theorems/9c3db6d3-06ef-46d0-af23-ccb5cf1a2096
-- title:
--   T: exists continuous norm Char LFunction ne zero one
-- statement:
--   The T construction uses the exists continuous norm Char LFunction ne zero one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsContinuousNormCharLFunctionNeZeroOneStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsContinuousNormCharLFunctionNeZeroOneStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsContinuousNormCharLFunctionNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsContinuousNormCharLFunctionNeZeroOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_continuous_normCharLFunction_ne_zero_one : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → ∀ (χ : (ZMod m)ˣ →* ℂˣ) (cl : HeightOneSpectrum (𝓞 K) → (ZMod m)ˣ), (∀ P, ¬ m ∣ Ideal.absNorm P.asIdeal → (cl P : ZMod m) = (Ideal.absNorm P.asIdeal : ℕ)) → (∃ P, ¬ m ∣ Ideal.absNorm P.asIdeal ∧ χ (cl P) ≠ 1) → ∃ L : ℂ → ℂ, Continuous L ∧ L 1 ≠ 0 ∧ ∀ s : ℝ, 1 < s → Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - ((χ (cl P) : ℂˣ) : ℂ) * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-(s : ℂ)))) = L s := by sorry
