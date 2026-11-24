-- Prove2me | Theorems.Thm_GlobalTheory_T_two_pow_card_le_index_iInf_of_independent
-- name    : GlobalTheory.T.two_pow_card_le_index_iInf_of_independent
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:59:40.850123+00:00
-- url     : https://prove2.me/theorems/6fe5282d-20a2-4913-a4f1-201eb434ed90
-- title:
--   T: two pow card le index i Inf of independent
-- statement:
--   The T construction uses the two pow card le index i Inf of independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TwoPowCardLeIndexIInfStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TwoPowCardLeIndexIInfStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoPowCardLeIndexIInf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoPowCardLeIndexIInfStatement
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

theorem GlobalTheory.T.two_pow_card_le_index_iInf_of_independent : ∀ (G ι : Type) [CommGroup G] [Fintype ι] (K : ι → Subgroup G), (∀ i, ∃ x, x ∉ K i ∧ ∀ j, j ≠ i → x ∈ K j) → (⨅ i, K i).index ≠ 0 → 2 ^ Fintype.card ι ≤ (⨅ i, K i).index := by sorry
