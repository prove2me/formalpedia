-- Prove2me | Theorems.Thm_GlobalTheory_CMLatticeRow_lc
-- name    : GlobalTheory.CMLatticeRow.lc
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:03:41.524752+00:00
-- url     : https://prove2.me/theorems/c6cc7b47-ab69-4c1b-b72b-27e0f157f6ce
-- title:
--   CMLattice Row: lc
-- statement:
--   The CMLattice Row construction uses the lc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PolarisationDualStatement.lean#L82-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PolarisationDualStatement.lean#L82-L83

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

theorem GlobalTheory.CMLatticeRow.lc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (O : Type) [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] (H : Type) [AddCommGroup H] [Module O H], Module.Free O H → ∀ (ρ : orderC c →+* Module.End O H) (B : LinearMap.BilinForm O H) (I : Type) [Fintype I] (N : I → Module.End K (K ⊗[O] H)) (D : O) (M : I → Module.End O H), (∀ i, IsScaledRestr D (N i) (M i)) → (∀ i (a : OF E), Commute (N i) ((ρ (ofF c a)).baseChange K)) → (∀ i j, N i * N j = 0) → (∀ i x y, B.baseChange K (N i x) y + B.baseChange K x (N i y) = 0) → (∀ i j x y, B.baseChange K (N i x) (N j y) = 0) → ∀ (l : ℕ) (R : Type) [CommRing R] [Algebra O R] (t : I → R), (∀ x : R ⊗[O] H, ∃ y : R ⊗[O] H, (1 + nilPart l M R t) x = x + (lPrime l : R) • y) ∧ ((1 + nilPart l M R t) * (1 - nilPart l M R t) = 1 ∧ (1 - nilPart l M R t) * (1 + nilPart l M R t) = 1) ∧ (∀ a : OF E, Commute (1 + nilPart l M R t) ((ρ (ofF c a)).baseChange R)) ∧ ∀ x y : R ⊗[O] H, B.baseChange R ((1 + nilPart l M R t) x) ((1 + nilPart l M R t) y) = B.baseChange R x y := by sorry
