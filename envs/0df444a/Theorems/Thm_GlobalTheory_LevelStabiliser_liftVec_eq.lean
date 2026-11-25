-- Prove2me | Theorems.Thm_GlobalTheory_LevelStabiliser_liftVec_eq
-- name    : GlobalTheory.LevelStabiliser.liftVec_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:21:13.693267+00:00
-- url     : https://prove2.me/theorems/9add6c4a-da2d-4dfa-b008-711c333e1d68
-- title:
--   Level Stabiliser: lift Vec eq
-- statement:
--   The Level Stabiliser construction uses the lift Vec eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LevMulVecOutside.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LevMulVecOutside.lean#L15-L18

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GramRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LevMulVecOutside
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
open GlobalTheory GlobalTheory.LevelStabiliser
open GlobalTheory.LevelUnitary
variable (k i r' : ℕ)

theorem GlobalTheory.LevelStabiliser.liftVec_eq (v : Fin (2 * r' + k + 1) → ℂ) : liftVec k i r' v = incl k i r' *ᵥ v := by sorry
