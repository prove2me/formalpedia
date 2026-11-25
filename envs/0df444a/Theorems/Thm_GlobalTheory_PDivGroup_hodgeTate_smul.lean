-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_hodgeTate_smul
-- name    : GlobalTheory.PDivGroup.hodgeTate_smul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:29:10.116588+00:00
-- url     : https://prove2.me/theorems/6e57cce4-ea87-4818-a062-910843367db5
-- title:
--   PDiv Group: hodge Tate smul
-- statement:
--   The PDiv Group construction uses the hodge Tate smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1048-L1050
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1048-L1050

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

theorem GlobalTheory.PDivGroup.hodgeTate_smul (φ : ℤ_[p] →+* O) (a : ℤ_[p]) (t : G.Tate) :
    hodgeTate G (a • t) = φ a • hodgeTate G t := by sorry
