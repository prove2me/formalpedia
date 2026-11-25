-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_baseChange
-- name    : GlobalTheory.QuadSymbol.baseChange
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:13:42.510034+00:00
-- url     : https://prove2.me/theorems/69a192ee-7267-4d22-941d-c63f731fa38f
-- title:
--   Quad Symbol: base Change
-- statement:
--   The Quad Symbol construction uses the base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IndexTwoOfFiniteReal.lean#L361-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IndexTwoOfFiniteReal.lean#L361-L372

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
open NormBaseChange

theorem GlobalTheory.QuadSymbol.baseChange : ∀ (F E K L : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra F E] [Algebra F K] [Algebra K L]
    [Algebra E L] [Algebra F L] [IsScalarTower F K L] [IsScalarTower F E L]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsQuadraticExtension K L],
    Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤ →
    (∀ v : HeightOneSpectrum (𝓞 F), BaseChangeAt F E K L (v.adicCompletion F)) ∧
    ∀ v : InfinitePlace F, BaseChangeAt F E K L v.Completion := by sorry
