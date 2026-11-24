-- Prove2me | Theorems.Thm_GlobalTheory_DualTransfer_exists_separating
-- name    : GlobalTheory.DualTransfer.exists_separating
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:51:53.495738+00:00
-- url     : https://prove2.me/theorems/eb95d79f-5bbc-43f5-802c-2f854ae918c8
-- title:
--   Dual Transfer: exists separating
-- statement:
--   The Dual Transfer construction uses the exists separating property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/DivisiblePontryaginAnnihilatorDuality.lean#L53-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/DivisiblePontryaginAnnihilatorDuality.lean#L53-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DivisiblePontryaginAnnihilatorDuality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DualTransfer

theorem GlobalTheory.DualTransfer.exists_separating {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A → B → ℂ)
    (h1 : ∀ a a' b, e (a + a') b = e a b * e a' b) (h2 : ∀ a b b', e a (b + b') = e a b * e a b')
    (h3 : ∀ b, e 0 b = 1) (h4 : ∀ a, e a 0 = 1) (M : AddSubgroup A) (K : AddSubgroup B)
    [Finite (A ⧸ M)] [Finite (B ⧸ K)]
    (hM : ∀ a, a ∈ M ↔ ∀ b, e a b = 1) (hK : ∀ b, b ∈ K ↔ ∀ a, e a b = 1)
    (H : AddSubgroup A) (hMH : M ≤ H) (x : A) (hx : x ∉ H) :
    ∃ b, (∀ u ∈ H, e u b = 1) ∧ e x b ≠ 1 := by sorry
