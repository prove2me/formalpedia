-- Prove2me | Theorems.Thm_GlobalTheory_T_index_unitsSquareUnderRingHom_adicCompletion_le
-- name    : GlobalTheory.T.index_unitsSquareUnderRingHom_adicCompletion_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:46:31.20974+00:00
-- url     : https://prove2.me/theorems/48629198-2857-421f-8bf2-6ffb98ff56e0
-- title:
--   T: index units Square Under Ring Hom adic Completion le
-- statement:
--   The T construction uses the index units Square Under Ring Hom adic Completion le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IndexUnitsSquareUnderRingHomAdicCompletionLeStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IndexUnitsSquareUnderRingHomAdicCompletionLeStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsSquareUnderRingHomAdicCompletionLe
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsSquareUnderRingHomAdicCompletionLeStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.index_unitsSquareUnderRingHom_adicCompletion_le : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : ℕ), v.valuation F 2 = WithZero.exp (-(e : ℤ)) → (sqSub (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧ (sqSub (algebraMap F (v.adicCompletion F))).index ≤ 4 * Ideal.absNorm v.asIdeal ^ e := by sorry
