-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_sqIdx_hiUnits_anti
-- name    : GlobalTheory.QNorm.sqIdx_hiUnits_anti
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:43:11.88008+00:00
-- url     : https://prove2.me/theorems/c400cf76-1dec-44c6-bc84-f95b506f00e3
-- title:
--   QNorm: sq Idx hi Units anti
-- statement:
--   The QNorm construction uses the sq Idx hi Units anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IndexUnitsSquareUnderRingHomAdicCompletionLe.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IndexUnitsSquareUnderRingHomAdicCompletionLe.lean#L14-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexSquaresLeTwoMulOfSubgroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HigherUnitsLeSquaresHigherUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsGlobalUniformizerResidueRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexHigherUnitsSuccLeCardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexSquaresLeTwoMulUnitsSquaresStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsSquareUnderRingHomAdicCompletionLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm

theorem GlobalTheory.QNorm.sqIdx_hiUnits_anti {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) {m n : ℕ} (h : m ≤ n) :
    hiUnits w n ≤ hiUnits w m := by sorry
