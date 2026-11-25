-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_TateOver_conv_succ_pow
-- name    : GlobalTheory.PDivGroup.TateOver.conv_succ_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:26:04.333334+00:00
-- url     : https://prove2.me/theorems/17c62788-d2dd-4c4e-8ce2-4544ee65450a
-- title:
--   Tate Over: conv succ pow
-- statement:
--   The Tate Over construction uses the conv succ pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L395-L398
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L395-L398

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
variable {G H K : PDivGroup p O} {B B' : Type} [CommRing B] [Algebra O B] [CommRing B']
  [Algebra O B']
open GlobalTheory.PDivGroup.TateOver

theorem GlobalTheory.PDivGroup.TateOver.conv_succ_pow (x : G.TateOver B) (n : ℕ) :
    x.conv (n + 1) ^ p = pointsMap B (G.res n) (x.conv n) := by sorry
