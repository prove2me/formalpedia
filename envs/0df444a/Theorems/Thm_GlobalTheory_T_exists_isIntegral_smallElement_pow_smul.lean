-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_isIntegral_smallElement_pow_smul
-- name    : GlobalTheory.T.exists_isIntegral_smallElement_pow_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:37:12.794344+00:00
-- url     : https://prove2.me/theorems/368c1542-3212-4a44-b15f-2b45671bb06f
-- title:
--   T: exists is Integral small Element pow smul
-- statement:
--   The T construction uses the exists is Integral small Element pow smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIsIntegralSmallElementPowSmulStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIsIntegralSmallElementPowSmulStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsIntegralSmallElementPowSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsIntegralSmallElementPowSmulStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_isIntegral_smallElement_pow_smul : ∀ (K : UQ) (B : InvAlg K) (a : K.O), K.Small a → ∀ x : B.A, ∃ k : ℕ, IsIntegral K.O ((al K a ^ k) • x) := by sorry
