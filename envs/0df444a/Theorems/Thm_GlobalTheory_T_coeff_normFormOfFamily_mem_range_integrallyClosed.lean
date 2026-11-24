-- Prove2me | Theorems.Thm_GlobalTheory_T_coeff_normFormOfFamily_mem_range_integrallyClosed
-- name    : GlobalTheory.T.coeff_normFormOfFamily_mem_range_integrallyClosed
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:31:06.87209+00:00
-- url     : https://prove2.me/theorems/df25d17f-6d14-4311-beae-18a5ef2e4014
-- title:
--   T: coeff norm Form Of Family mem range integrally Closed
-- statement:
--   The T construction uses the coeff norm Form Of Family mem range integrally Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffNormFormOfFamilyMemRangeIntegrallyClosedStatement.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffNormFormOfFamilyMemRangeIntegrallyClosedStatement.lean#L9-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffNormFormOfFamilyMemRangeIntegrallyClosed
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffNormFormOfFamilyMemRangeIntegrallyClosedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.coeff_normFormOfFamily_mem_range_integrallyClosed : ∀ (A K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Field L] [Algebra A K]
    [IsFractionRing A K] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L] {m : ℕ}
    (x : Fin m → L), (∀ i, IsIntegral A (x i)) →
    ∀ s, (GlobalTheory.NormSheaf.normForm K L x).coeff s ∈ (algebraMap A K).range := by sorry
