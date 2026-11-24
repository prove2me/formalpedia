-- Prove2me | Theorems.Thm_GlobalTheory_T_relIndex_squares_sUnitsNumberField
-- name    : GlobalTheory.T.relIndex_squares_sUnitsNumberField
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:56:16.228917+00:00
-- url     : https://prove2.me/theorems/5ceeb1a7-4e2a-48ed-bbde-c5e883a89a2d
-- title:
--   T: rel Index squares s Units Number Field
-- statement:
--   The T construction uses the rel Index squares s Units Number Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/RelIndexSquaresSUnitsNumberFieldStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/RelIndexSquaresSUnitsNumberFieldStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexSquaresSUnitsNumberField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexSquaresSUnitsNumberFieldStatement
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

theorem GlobalTheory.T.relIndex_squares_sUnitsNumberField : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), (sqs (sUnits F S)).relIndex (sUnits F S) = 2 ^ (S.card + Fintype.card (InfinitePlace F)) := by sorry
