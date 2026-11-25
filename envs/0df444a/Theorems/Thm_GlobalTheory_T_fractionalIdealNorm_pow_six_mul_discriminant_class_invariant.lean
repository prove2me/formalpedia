-- Prove2me | Theorems.Thm_GlobalTheory_T_fractionalIdealNorm_pow_six_mul_discriminant_class_invariant
-- name    : GlobalTheory.T.fractionalIdealNorm_pow_six_mul_discriminant_class_invariant
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:32:05.8888+00:00
-- url     : https://prove2.me/theorems/dffbf6f7-9973-5c49-9ad8-66a17fa0bd15
-- title:
--   T: fractional Ideal Norm pow six mul discriminant class invariant
-- statement:
--   The T construction uses the fractional Ideal Norm pow six mul discriminant class invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FractionalIdealNormPowSixMulDiscriminantClassInvStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FractionalIdealNormPowSixMulDiscriminantClassInvStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FractionalIdealNormPowSixMulDiscriminantClassInv
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FractionalIdealNormPowSixMulDiscriminantClassInvStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.fractionalIdealNorm_pow_six_mul_discriminant_class_invariant : ∀ {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ), Module.finrank ℚ K = 2 → (starRingEnd ℂ).comp φK ≠ φK → ∀ (𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λa Λb : PeriodPair), IsLatOf φK (𝔞 : FractionalIdeal (𝓞 K)⁰ K) Λa → IsLatOf φK (𝔟 : FractionalIdeal (𝓞 K)⁰ K) Λb → ClassGroup.mk K 𝔞 = ClassGroup.mk K 𝔟 → nrm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc Λa‖ = nrm (𝔟 : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc Λb‖ := by sorry
