-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertIndex_mem_intL_iff
-- name    : GlobalTheory.CompanionTheory.InertIndex.mem_intL_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:45:37.881941+00:00
-- url     : https://prove2.me/theorems/ff50379a-e352-4450-9261-ffb23626e8e6
-- title:
--   Inert Index: mem int L iff
-- statement:
--   The Inert Index construction uses the mem int L iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/LatticeIndexOfSmith.lean#L42-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/LatticeIndexOfSmith.lean#L42-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqProd
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_LatticeIndexOfSmith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.BorelUMod.UpLatIndex
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertIndex
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem GlobalTheory.CompanionTheory.InertIndex.mem_intL_iff {x : L} : x ∈ intL L ↔ Valued.v x ≤ 1 := by sorry
