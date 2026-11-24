-- Prove2me | Theorems.Thm_GlobalTheory_PowEntryCommutator_pow_entry_commutator
-- name    : GlobalTheory.PowEntryCommutator.pow_entry_commutator
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:52:35.368073+00:00
-- url     : https://prove2.me/theorems/e94998ad-c844-439d-a038-2e88f0938b4f
-- title:
--   Pow Entry Commutator: pow entry commutator
-- statement:
--   The Pow Entry Commutator construction uses the pow entry commutator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PowEntryCommutator.lean#L7-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PowEntryCommutator.lean#L7-L33

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

theorem GlobalTheory.PowEntryCommutator.pow_entry_commutator {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : Formalism.REAL.GlRel E) (a b : Fin n) (m : ℕ) (c e : Fin n) :
    E a b * ((Matrix.of E) ^ m) c e - ((Matrix.of E) ^ m) c e * E a b =
      (if b = c then ((Matrix.of E) ^ m) a e else 0) -
        (if e = a then ((Matrix.of E) ^ m) c b else 0) := by sorry
