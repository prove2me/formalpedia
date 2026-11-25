-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticValuationIndexTwo_norm_index_two
-- name    : GlobalTheory.QuadraticValuationIndexTwo.norm_index_two
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:14:03.859685+00:00
-- url     : https://prove2.me/theorems/dbb87b52-7cd9-4df1-a5a5-f39048336617
-- title:
--   Quadratic Valuation Index Two: norm index two
-- statement:
--   The Quadratic Valuation Index Two construction uses the norm index two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSubgroupIndexTwo.lean#L173-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSubgroupIndexTwo.lean#L173-L198

import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsKum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CyclicKummerNormFixedHilbert90
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HerbrandPrimeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PIdxUnitsFiniteExtensionAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSubgroupIndexTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CNorm GlobalTheory.QuadSymbol.NormIndex
open GlobalTheory GlobalTheory.QuadraticValuationIndexTwo

theorem GlobalTheory.QuadraticValuationIndexTwo.norm_index_two (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (B : Type) [Field B] [Algebra (v.adicCompletion F) B]
    [FiniteDimensional (v.adicCompletion F) B] (d : B) (hd : ¬ IsSquare d) :
    (∃ c : B, c ≠ 0 ∧ ¬ Nm d c) ∧
      ∀ x y : B, x ≠ 0 → y ≠ 0 → ¬ Nm d x → ¬ Nm d y → Nm d (x * y) := by sorry
