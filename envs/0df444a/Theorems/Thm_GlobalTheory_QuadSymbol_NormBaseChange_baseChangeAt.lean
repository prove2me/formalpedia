-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_NormBaseChange_baseChangeAt
-- name    : GlobalTheory.QuadSymbol.NormBaseChange.baseChangeAt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:12:45.265307+00:00
-- url     : https://prove2.me/theorems/1a4b64c1-8f3b-452b-a4c5-b514a949efce
-- title:
--   Norm Base Change: base Change At
-- statement:
--   The Norm Base Change construction uses the base Change At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IndexTwoOfFiniteReal.lean#L320-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IndexTwoOfFiniteReal.lean#L320-L355

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsKum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CyclicKummerNormFixedHilbert90
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HerbrandPrimeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PIdxUnitsFiniteExtensionAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSubgroupIndexTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndexTwoOfFiniteReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.QuadSymbol
open GlobalTheory.QuadSymbol.NormBaseChange
open NormIndex

theorem GlobalTheory.QuadSymbol.NormBaseChange.baseChangeAt (F E K L A : Type) [Field F] [CharZero F] [Field E] [Field K] [Field L]
    [Field A] [Algebra F E] [Algebra F K] [Algebra K L] [Algebra E L] [Algebra F L] [Algebra F A]
    [IsScalarTower F K L] [IsScalarTower F E L] (hE : Module.finrank F E = 2)
    (hL : Module.finrank K L = 2) (hgen : Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤)
    (hA : ∀ (B : Type) [Field B] [Algebra A B] [FiniteDimensional A B], IndexTwo B) :
    BaseChangeAt F E K L A := by sorry
