-- Prove2me | Theorems.Thm_GlobalTheory_CMLatticeRow_dp1
-- name    : GlobalTheory.CMLatticeRow.dp1
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:03:39.489263+00:00
-- url     : https://prove2.me/theorems/c07f69ca-2ff0-4246-a7c0-acc53c144740
-- title:
--   CMLattice Row: dp1
-- statement:
--   The CMLattice Row construction uses the dp1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PolarisationDualStatement.lean#L97-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PolarisationDualStatement.lean#L97-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_DividedPowersValuationsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentConductorIffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentOfExponentBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentOfTraceDualStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftOfTraceDualElementStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDifferentExponentDenominatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValVpNatCastPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralFirstStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralSecondStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralThirdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralFourthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralFifthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodDenominatorBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodValuationBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodConjugateIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodProductIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScaledRestrictionEndomorphismsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodTraceIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodNormIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodGaloisIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowersPrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DividedPowersPrimeUniqueStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarisationDualStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.CMLatticeRow

theorem GlobalTheory.CMLatticeRow.dp1 : ∀ (l : ℕ), l.Prime → (∀ m : ℕ, (1 ≤ m → lPrimeExp l + padicValNat l m.factorial ≤ lPrimeExp l * m) ∧ m + 2 * padicValNat l m.factorial ≤ 2 * (lPrimeExp l * m)) → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ (R : Type) [CommRing R] [Algebra O R], (∀ (k : ℕ) (x : R), k ≠ 0 → (k : R) * x = 0 → x = 0) → ∀ γ₀ : DividedPowers (Ideal.span {(l : R)}), (∀ (m : ℕ), ∀ y ∈ Ideal.span {(l : R)}, (m.factorial : R) * γ₀.dpow m y = y ^ m) → ∃ γ : DividedPowers (Ideal.span {(lPrime l : R)}), (∀ m : ℕ, ∃ q : O, (m.factorial : O) * q = (lPrime l : O) ^ m ∧ ∀ x : R, γ.dpow m ((lPrime l : R) * x) = algebraMap O R q * x ^ m) ∧ (∀ (m : ℕ), ∀ y ∈ Ideal.span {(lPrime l : R)}, γ.dpow m y = γ₀.dpow m y) ∧ ∀ n : ℕ, 1 ≤ n → γ.IsSubDPIdeal (Ideal.span {(lPrime l : R) ^ n}) ∧ ∀ (r : ℕ) (m : Fin r → ℕ) (x : Fin r → R), (∀ i, x i ∈ Ideal.span {(lPrime l : R)}) → 2 * n * lPrimeExp l ≤ ∑ i, m i → ∏ i, γ.dpow (m i) (x i) ∈ Ideal.span {(lPrime l : R) ^ n} := by sorry
