-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertIndex_mem_preLat_iff
-- name    : GlobalTheory.CompanionTheory.InertIndex.mem_preLat_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:02:16.053042+00:00
-- url     : https://prove2.me/theorems/dca99e3e-b3a7-4da3-81c8-c579fda1be1b
-- title:
--   Inert Index: mem pre Lat iff
-- statement:
--   The Inert Index construction uses the mem pre Lat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/LatticeIndexOfSmith.lean#L55-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/LatticeIndexOfSmith.lean#L55-L73

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

theorem GlobalTheory.CompanionTheory.InertIndex.mem_preLat_iff {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {d : Fin n → ℤ}
    {a b b' : Matrix (Fin n) (Fin n) L} (hb : IsInt b) (hb' : IsInt b') (eb : b * b' = 1) (r : Fin n → L) :
    r ∈ preLat (a * Matrix.diagonal (fun i => ϖ ^ d i) * b) ↔ r ᵥ* a ∈ boxLat L (fun i => -d i) := by sorry
