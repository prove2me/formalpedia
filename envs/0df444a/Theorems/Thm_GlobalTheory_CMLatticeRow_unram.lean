-- Prove2me | Theorems.Thm_GlobalTheory_CMLatticeRow_unram
-- name    : GlobalTheory.CMLatticeRow.unram
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:05:24.131624+00:00
-- url     : https://prove2.me/theorems/b9c50c97-2dad-4576-91d6-f54a09bdeff1
-- title:
--   CMLattice Row: unram
-- statement:
--   The CMLattice Row construction uses the unram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PolarisationDualStatement.lean#L43-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PolarisationDualStatement.lean#L43-L44

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

theorem GlobalTheory.CMLatticeRow.unram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ), l.Prime → ¬ (l : ℤ) ∣ discr E → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) → ∃ z : O, algebraMap O K z = σ y := by sorry
