-- Prove2me | Theorems.Thm_GlobalTheory_doubleCoset_fibre_card
-- name    : GlobalTheory.doubleCoset_fibre_card
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:16:34.44891+00:00
-- url     : https://prove2.me/theorems/98ab6849-0a3c-42fa-bbc7-0717d1114a26
-- title:
--   Global Theory: double Coset fibre card
-- statement:
--   The Global Theory construction uses the double Coset fibre card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardFiberDoubleCosetMapEqCardInfConj.lean#L6-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardFiberDoubleCosetMapEqCardInfConj.lean#L6-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardFiberDoubleCosetMapEqCardInfConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Pointwise
open GlobalTheory

theorem GlobalTheory.doubleCoset_fibre_card {G : Type} [Group G] (T Γ K' : Subgroup G) (x : G) :
    Nat.card ((fun q : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G) =>
        DoubleCoset.mk T K' (Quotient.out q)) ⁻¹' {DoubleCoset.mk T K' x}) =
      Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T)
        (((T ⊓ K'.map (MulAut.conj x).toMonoidHom).subgroupOf T : Subgroup T) : Set T)) := by sorry
