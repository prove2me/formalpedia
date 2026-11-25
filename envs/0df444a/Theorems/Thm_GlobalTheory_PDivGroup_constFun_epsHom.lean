-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_constFun_epsHom
-- name    : GlobalTheory.PDivGroup.constFun_epsHom
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:15:21.038918+00:00
-- url     : https://prove2.me/theorems/5288c384-0ff1-5b14-816a-507d4c105926
-- title:
--   PDiv Group: const Fun eps Hom
-- statement:
--   The PDiv Group construction uses the const Fun eps Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1078-L1082
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1078-L1082

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
open GlobalTheory
open PDiv
open GlobalTheory.PDivGroup
attribute [instance] commRing hopf cocomm finite projective
variable {p : ℕ} {O : Type} [CommRing O]
variable {G H : PDivGroup p O}
variable [Fact p.Prime]

theorem GlobalTheory.PDivGroup.constFun_epsHom (ζ : ℕ → O) (h0 : ζ 0 = 1) (h : ∀ n, ζ (n + 1) ^ p = ζ n) (n k : ℕ) :
    constFun p O n ((epsHom ζ h0 h).app n (muT O _)) k = ζ n ^ k := by sorry
