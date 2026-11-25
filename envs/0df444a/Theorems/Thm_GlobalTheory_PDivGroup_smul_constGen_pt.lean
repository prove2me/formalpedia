-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_smul_constGen_pt
-- name    : GlobalTheory.PDivGroup.smul_constGen_pt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:27:27.363575+00:00
-- url     : https://prove2.me/theorems/74d76085-dcb2-4bac-97a2-defbb58c0fac
-- title:
--   PDiv Group: smul const Gen pt
-- statement:
--   The PDiv Group construction uses the smul const Gen pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1238-L1244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1238-L1244

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
variable (p O) [Fact p.Prime]

theorem GlobalTheory.PDivGroup.smul_constGen_pt (a : ℤ_[p]) (n : ℕ) (φ : (const p O).A n) :
    (a • constGen p O).pt n φ = constFun p O n φ (PadicInt.toZModPow n a) := by sorry
