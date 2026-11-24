-- Prove2me | Theorems.Thm_GlobalTheory_RegularElementQuotient_maximalIdeal_smul_top_lt_top
-- name    : GlobalTheory.RegularElementQuotient.maximalIdeal_smul_top_lt_top
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:19:43.057003+00:00
-- url     : https://prove2.me/theorems/10ff1bf3-167e-4858-aab4-9fdb9d48621d
-- title:
--   Regular Element Quotient: maximal Ideal smul top lt top
-- statement:
--   The Regular Element Quotient construction uses the maximal Ideal smul top lt top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsIsRegularQuotSMulTop.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsIsRegularQuotSMulTop.lean#L9-L18

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

theorem GlobalTheory.RegularElementQuotient.maximalIdeal_smul_top_lt_top {R : Type u_1} [CommRing R] [IsLocalRing R]
    (M : Type u_2) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) < ⊤ := by sorry
