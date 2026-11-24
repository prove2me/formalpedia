-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertIndex_relIndex_boxLat
-- name    : GlobalTheory.CompanionTheory.InertIndex.relIndex_boxLat
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:02:28.924155+00:00
-- url     : https://prove2.me/theorems/56782234-6017-4c36-ac60-7f02788b52d6
-- title:
--   Inert Index: rel Index box Lat
-- statement:
--   The Inert Index construction uses the rel Index box Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/LatticeIndexOfSmith.lean#L20-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/LatticeIndexOfSmith.lean#L20-L40

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

theorem GlobalTheory.CompanionTheory.InertIndex.relIndex_boxLat (c C : Fin n → ℤ) :
    (boxLat L C).relIndex (boxLat L c) = ∏ i, (ordBall L (C i)).relIndex (ordBall L (c i)) := by sorry
