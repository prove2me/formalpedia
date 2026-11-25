-- Prove2me | Theorems.Thm_GlobalTheory_LevelUnitary_mul_incl
-- name    : GlobalTheory.LevelUnitary.mul_incl
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:50:34.028422+00:00
-- url     : https://prove2.me/theorems/81707bbe-f970-4376-a316-fd5daab6169a
-- title:
--   Level Unitary: mul incl
-- statement:
--   The Level Unitary construction uses the mul incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GramRight.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GramRight.lean#L18-L20

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

theorem GlobalTheory.LevelUnitary.mul_incl {m : Type} (M : Matrix m (Fin (2 * (i + r') + k + 1)) ℂ) (p : m) (j) :
    (M * incl k i r') p j = M p (levPos k i r' j) := by sorry
