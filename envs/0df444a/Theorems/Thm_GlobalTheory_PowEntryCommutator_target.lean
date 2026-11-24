-- Prove2me | Theorems.Thm_GlobalTheory_PowEntryCommutator_target
-- name    : GlobalTheory.PowEntryCommutator.target
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:51:47.042209+00:00
-- url     : https://prove2.me/theorems/38c721c0-7c91-48c2-969f-bb01c7aafca6
-- title:
--   Pow Entry Commutator: target
-- statement:
--   The Pow Entry Commutator construction uses the target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PowEntryCommutator.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PowEntryCommutator.lean#L35-L43

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PowEntryCommutator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowEntryCommutator
open Matrix

theorem GlobalTheory.PowEntryCommutator.target : ∀ {A : Type} [inst : Ring A] {n : ℕ} (E : Fin n → Fin n → A), Formalism.REAL.GlRel E →
    ∀ (a b : Fin n) (m : ℕ) (c e : Fin n),
    E a b * ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ m) c e -
      ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ m) c e * E a b =
    (if b = c then ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ m) a e
      else (0 : A)) -
    if e = a then ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ m) c b
      else (0 : A) := by sorry
