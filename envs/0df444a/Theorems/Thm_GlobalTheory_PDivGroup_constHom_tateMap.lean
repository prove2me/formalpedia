-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_constHom_tateMap
-- name    : GlobalTheory.PDivGroup.constHom_tateMap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:25:57.947798+00:00
-- url     : https://prove2.me/theorems/60b3f93e-8680-423e-a72b-a2d17b5409d9
-- title:
--   PDiv Group: const Hom tate Map
-- statement:
--   The PDiv Group construction uses the const Hom tate Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1024-L1026
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1024-L1026

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

theorem GlobalTheory.PDivGroup.constHom_tateMap (f : G ⟶ H) (t : G.Tate) :
    constHom H (tateMap G H O f t) = constHom G t ≫ f := by sorry
