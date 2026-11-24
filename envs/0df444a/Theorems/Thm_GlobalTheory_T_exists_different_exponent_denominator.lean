-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_different_exponent_denominator
-- name    : GlobalTheory.T.exists_different_exponent_denominator
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:34:08.525951+00:00
-- url     : https://prove2.me/theorems/67ac853d-f0db-44b4-ac43-556113906f77
-- title:
--   T: exists different exponent denominator
-- statement:
--   The T construction uses the exists different exponent denominator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDifferentExponentDenominatorStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDifferentExponentDenominatorStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDifferentExponentDenominator
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDifferentExponentDenominatorStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_different_exponent_denominator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∃ D : O, (∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal → val_vp O l (algebraMap O K D) = ((diffExp_vp l P : ℚ) : WithTop ℚ)) ∧ ∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) → ∃ z : O, algebraMap O K z = algebraMap O K D * σ y := by sorry
