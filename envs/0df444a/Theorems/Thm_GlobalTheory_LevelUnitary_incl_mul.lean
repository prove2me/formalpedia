-- Prove2me | Theorems.Thm_GlobalTheory_LevelUnitary_incl_mul
-- name    : GlobalTheory.LevelUnitary.incl_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:56:09.439803+00:00
-- url     : https://prove2.me/theorems/0812cf80-5df8-4ee6-a49b-b91c721fc859
-- title:
--   Level Unitary: incl mul
-- statement:
--   The Level Unitary construction uses the incl mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GramRight.lean#L26-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GramRight.lean#L26-L49

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GramRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
noncomputable section
open GlobalTheory GlobalTheory.LevelUnitary
variable (k i r' : ℕ)

theorem GlobalTheory.LevelUnitary.incl_mul {m : Type} (M : Matrix (Fin (2 * r' + k + 1)) m ℂ) (p) (q : m) :
    (incl k i r' * M) p q =
      if hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i then M ⟨p.val - i, by omega⟩ q else 0 := by sorry
