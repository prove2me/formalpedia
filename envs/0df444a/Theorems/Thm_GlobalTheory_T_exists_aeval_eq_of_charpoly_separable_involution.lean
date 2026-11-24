-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_aeval_eq_of_charpoly_separable_involution
-- name    : GlobalTheory.T.exists_aeval_eq_of_charpoly_separable_involution
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:37:57.650528+00:00
-- url     : https://prove2.me/theorems/ee8e04ad-a195-49a9-918c-e437f7137af4
-- title:
--   T: exists aeval eq of charpoly separable involution
-- statement:
--   The T construction uses the exists aeval eq of charpoly separable involution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAevalEqOfCharpolySeparableInvolutionStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAevalEqOfCharpolySeparableInvolutionStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfCharpolySeparableInvolution
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfCharpolySeparableInvolutionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_aeval_eq_of_charpoly_separable_involution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f := by sorry
