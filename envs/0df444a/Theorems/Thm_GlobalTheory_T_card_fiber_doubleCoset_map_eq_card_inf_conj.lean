-- Prove2me | Theorems.Thm_GlobalTheory_T_card_fiber_doubleCoset_map_eq_card_inf_conj
-- name    : GlobalTheory.T.card_fiber_doubleCoset_map_eq_card_inf_conj
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:27:59.499103+00:00
-- url     : https://prove2.me/theorems/6100fe40-202f-4fc3-8307-96c3a3eea208
-- title:
--   T: card fiber double Coset map eq card inf conj
-- statement:
--   The T construction uses the card fiber double Coset map eq card inf conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardFiberDoubleCosetMapEqCardInfConjStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardFiberDoubleCosetMapEqCardInfConjStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardFiberDoubleCosetMapEqCardInfConj
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardFiberDoubleCosetMapEqCardInfConjStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Pointwise
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_fiber_doubleCoset_map_eq_card_inf_conj : ∀ {G : Type} [Group G] (T Γ K' : Subgroup G) (x : G), Nat.card ((fun q : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G) => DoubleCoset.mk T K' (Quotient.out q)) ⁻¹' {DoubleCoset.mk T K' x}) = Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T) (((T ⊓ K'.map (MulAut.conj x).toMonoidHom).subgroupOf T : Subgroup T) : Set T)) := by sorry
