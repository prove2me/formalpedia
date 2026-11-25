-- Prove2me | Theorems.Thm_GlobalTheory_Proof_DoubleCosetCountGlobalInterpolation_card_fiber_mul_card_stab
-- name    : GlobalTheory.Proof.DoubleCosetCountGlobalInterpolation.card_fiber_mul_card_stab
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:59:08.647154+00:00
-- url     : https://prove2.me/theorems/032a48cc-91ec-435a-a2a6-844a68617ab6
-- title:
--   Double Coset Count Global Interpolation: card fiber mul card stab
-- statement:
--   The Double Coset Count Global Interpolation construction uses the card fiber mul card stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DoubleCosetCount.lean#L8-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DoubleCosetCount.lean#L8-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_StabiliserCardinality
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DoubleCosetCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.DoubleCosetCountGlobalInterpolation
open GlobalTheory.IndefiniteRowSideFullHecke.StabiliserCardinality

theorem GlobalTheory.Proof.DoubleCosetCountGlobalInterpolation.card_fiber_mul_card_stab {G : Type} [Group G] (Γ U K : Subgroup G) (hUK : U ≤ K)
    (hfree : ∀ x : G, stab Γ U x = ⊥) (y : G) :
    Nat.card {d : DoubleCoset.Quotient (Γ : Set G) (U : Set G) //
        DoubleCoset.mk Γ K d.out = DoubleCoset.mk Γ K y} * Nat.card (stab Γ K y) =
      U.relIndex K := by sorry
