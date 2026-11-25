-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_exists_algHom_pi_eq_eval
-- name    : GlobalTheory.PDivGroup.exists_algHom_pi_eq_eval
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:41:43.051091+00:00
-- url     : https://prove2.me/theorems/c1473d54-ef7f-4a4f-88a5-2802a16c1d4c
-- title:
--   PDiv Group: exists alg Hom pi eq eval
-- statement:
--   The PDiv Group construction uses the exists alg Hom pi eq eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ToSpanSingletonConstGenSurjective.lean#L12-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ToSpanSingletonConstGenSurjective.lean#L12-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ToSpanSingletonConstGenSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup

theorem GlobalTheory.PDivGroup.exists_algHom_pi_eq_eval {O ι : Type*} [CommRing O] [Nontrivial O] [Finite ι]
    (hO : ∀ e : O, IsIdempotentElem e → e = 0 ∨ e = 1) (f : (ι → O) →ₐ[O] O) :
    ∃ k, ∀ g, f g = g k := by sorry
