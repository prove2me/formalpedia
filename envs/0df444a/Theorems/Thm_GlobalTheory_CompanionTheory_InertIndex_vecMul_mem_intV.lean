-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertIndex_vecMul_mem_intV
-- name    : GlobalTheory.CompanionTheory.InertIndex.vecMul_mem_intV
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:45:10.976795+00:00
-- url     : https://prove2.me/theorems/751427f6-e10f-450d-800e-ac72f5424379
-- title:
--   Inert Index: vec Mul mem int V
-- statement:
--   The Inert Index construction uses the vec Mul mem int V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/LatticeIndexOfSmith.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/LatticeIndexOfSmith.lean#L44-L49

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

theorem GlobalTheory.CompanionTheory.InertIndex.vecMul_mem_intV {M : Matrix (Fin n) (Fin n) L} (hM : IsInt M) {r : Fin n → L} (hr : r ∈ intV L n) :
    r ᵥ* M ∈ intV L n := by sorry
