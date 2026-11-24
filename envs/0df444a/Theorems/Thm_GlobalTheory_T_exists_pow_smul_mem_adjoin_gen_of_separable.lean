-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_pow_smul_mem_adjoin_gen_of_separable
-- name    : GlobalTheory.T.exists_pow_smul_mem_adjoin_gen_of_separable
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:37:50.912822+00:00
-- url     : https://prove2.me/theorems/def8e5ba-4f80-40cb-b37d-e7387c1907ac
-- title:
--   T: exists pow smul mem adjoin gen of separable
-- statement:
--   The T construction uses the exists pow smul mem adjoin gen of separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowSmulMemAdjoinGenStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowSmulMemAdjoinGenStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowSmulMemAdjoinGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowSmulMemAdjoinGenStatement
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

theorem GlobalTheory.T.exists_pow_smul_mem_adjoin_gen_of_separable : ∀ (K : UQ) (B : InvAlg K) (a : K.O), B.P.Separable → K.Small a → ∃ N : ℕ, ∀ r : B.A, IsIntegral K.O r → (al K a ^ N) • r ∈ Algebra.adjoin K.O {B.g} := by sorry
