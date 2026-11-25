-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_lieMap_charHom
-- name    : GlobalTheory.PDivGroup.lieMap_charHom
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:26:32.977162+00:00
-- url     : https://prove2.me/theorems/62083e5b-3841-4287-a38c-9c7563a0c872
-- title:
--   PDiv Group: lie Map char Hom
-- statement:
--   The PDiv Group construction uses the lie Map char Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1230-L1236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1230-L1236

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
variable {p O}

theorem GlobalTheory.PDivGroup.lieMap_charHom [IsAdicComplete (Ideal.span {(p : O)}) O] {G : PDivGroup p O}
    (χ : G.dual.Tate) (x : G.Lie) :
    lieMap G (mu p O) (charHom G χ) x = x (dlog G χ) • muLieGen p O := by sorry
