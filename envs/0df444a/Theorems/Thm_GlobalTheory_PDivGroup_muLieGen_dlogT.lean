-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
-- name    : GlobalTheory.PDivGroup.muLieGen_dlogT
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:28:32.68552+00:00
-- url     : https://prove2.me/theorems/9466710a-ced6-4a4e-806a-cc143353a214
-- title:
--   PDiv Group: mu Lie Gen dlog T
-- statement:
--   The PDiv Group construction uses the mu Lie Gen dlog T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1224-L1226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1224-L1226

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

theorem GlobalTheory.PDivGroup.muLieGen_dlogT [IsAdicComplete (Ideal.span {(p : O)}) O] :
    muLieGen p O (dlogT p O) = 1 := by sorry
