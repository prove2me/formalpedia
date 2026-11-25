-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_tatePush_bijective
-- name    : GlobalTheory.PDivGroup.tatePush_bijective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:22:42.197389+00:00
-- url     : https://prove2.me/theorems/ff7ff92e-70d9-441b-9120-94d68225937d
-- title:
--   PDiv Group: tate Push bijective
-- statement:
--   The PDiv Group construction uses the tate Push bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L503-L517
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L503-L517

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
variable [Fact p.Prime]
variable (G B)

theorem GlobalTheory.PDivGroup.tatePush_bijective [IsIntegrallyClosedIn O B] :
    Function.Bijective (G.tatePush (Algebra.ofId O B)) := by sorry
