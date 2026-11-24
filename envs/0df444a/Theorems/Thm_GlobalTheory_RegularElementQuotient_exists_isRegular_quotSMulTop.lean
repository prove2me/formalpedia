-- Prove2me | Theorems.Thm_GlobalTheory_RegularElementQuotient_exists_isRegular_quotSMulTop
-- name    : GlobalTheory.RegularElementQuotient.exists_isRegular_quotSMulTop
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:19:37.332719+00:00
-- url     : https://prove2.me/theorems/7a4253b2-04b3-4102-ab78-a9a13d34c9d1
-- title:
--   Regular Element Quotient: exists is Regular quot SMul Top
-- statement:
--   The Regular Element Quotient construction uses the exists is Regular quot SMul Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsIsRegularQuotSMulTop.lean#L20-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsIsRegularQuotSMulTop.lean#L20-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsIsRegularQuotSMulTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open CategoryTheory Abelian Limits RingTheory.Sequence Pointwise
open GlobalTheory GlobalTheory.RegularElementQuotient

theorem GlobalTheory.RegularElementQuotient.exists_isRegular_quotSMulTop {R : Type u_1} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [Small.{u_2, u_1} R] {M : Type u_2} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {xs : List R} (hxs : IsRegular M xs) {n : ℕ}
    (hn : n + 1 ≤ xs.length) {y : R} (hy : y ∈ IsLocalRing.maximalIdeal R)
    (hreg : IsSMulRegular M y) :
    ∃ zs : List R, zs.length = n ∧ IsRegular (QuotSMulTop y M) zs := by sorry
