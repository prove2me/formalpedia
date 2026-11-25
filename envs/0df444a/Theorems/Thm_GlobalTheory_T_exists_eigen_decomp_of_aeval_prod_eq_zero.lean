-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_eigen_decomp_of_aeval_prod_eq_zero
-- name    : GlobalTheory.T.exists_eigen_decomp_of_aeval_prod_eq_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:01:25.060085+00:00
-- url     : https://prove2.me/theorems/6584daaa-ccff-475d-8c3f-f77ef52a26ce
-- title:
--   T: exists eigen decomp of aeval prod eq zero
-- statement:
--   The T construction uses the exists eigen decomp of aeval prod eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumEigenvectorsOfAevalProdLinearEqZeroStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumEigenvectorsOfAevalProdLinearEqZeroStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumEigenvectorsOfAevalProdLinearEqZero
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumEigenvectorsOfAevalProdLinearEqZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_eigen_decomp_of_aeval_prod_eq_zero : ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (n : ℕ) (Ω : Module.End ℂ N) (ν : Fin n → ℂ), Function.Injective ν → Polynomial.aeval (-Ω) (∏ s, (Polynomial.X + Polynomial.C (ν s))) = 0 → ∀ w : N, ∃ v : Fin n → N, (∀ s, Ω (v s) = ν s • v s) ∧ w = ∑ s, v s := by sorry
