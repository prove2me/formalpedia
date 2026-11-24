-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_index_sqSub_adicCompletion_le
-- name    : GlobalTheory.QNorm.index_sqSub_adicCompletion_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:02:45.840023+00:00
-- url     : https://prove2.me/theorems/4599a8d5-d787-40c7-a6e9-1dc5e55cf4e7
-- title:
--   QNorm: index sq Sub adic Completion le
-- statement:
--   The QNorm construction uses the index sq Sub adic Completion le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IndexUnitsSquareUnderRingHomAdicCompletionLe.lean#L55-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IndexUnitsSquareUnderRingHomAdicCompletionLe.lean#L55-L84

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

theorem GlobalTheory.QNorm.index_sqSub_adicCompletion_le : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : ℕ), v.valuation F 2 = WithZero.exp (-(e : ℤ)) → (sqSub (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧ (sqSub (algebraMap F (v.adicCompletion F))).index ≤ 4 * Ideal.absNorm v.asIdeal ^ e := by sorry
