-- Prove2me | Theorems.Thm_GlobalTheory_mem_sup_of_isSMulRegular_quotient_quotient
-- name    : GlobalTheory.mem_sup_of_isSMulRegular_quotient_quotient
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:11:38.915574+00:00
-- url     : https://prove2.me/theorems/3e55e80a-b969-4e97-b034-ee66d90766d1
-- title:
--   Global Theory: mem sup of is SMul Regular quotient quotient
-- statement:
--   The Global Theory construction uses the mem sup of is SMul Regular quotient quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FlatQuotientWeaklyRegular.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FlatQuotientWeaklyRegular.lean#L40-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatCokerOfInjectiveModMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatQuotientWeaklyRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.mem_sup_of_isSMulRegular_quotient_quotient {A : Type} [CommRing A] (I J : Ideal A) (r : A)
    (h : IsSMulRegular ((A ⧸ I) ⧸ (J • ⊤ : Submodule A (A ⧸ I))) r) (a : A)
    (ha : r * a ∈ J ⊔ I) : a ∈ J ⊔ I := by sorry
