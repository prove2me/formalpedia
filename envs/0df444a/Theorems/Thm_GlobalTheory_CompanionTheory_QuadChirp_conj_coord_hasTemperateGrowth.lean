-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QuadChirp_conj_coord_hasTemperateGrowth
-- name    : GlobalTheory.CompanionTheory.QuadChirp.conj_coord_hasTemperateGrowth
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:55:43.902137+00:00
-- url     : https://prove2.me/theorems/6dbf9d31-a60b-4be4-b2a5-e6ac997ae924
-- title:
--   Quad Chirp: conj coord has Temperate Growth
-- statement:
--   The Quad Chirp construction uses the conj coord has Temperate Growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SchwartzQuadraticPhaseMultiplication.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SchwartzQuadraticPhaseMultiplication.lean#L22-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzQuadraticPhaseMultiplication
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix SchwartzMap ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QuadChirp

theorem GlobalTheory.CompanionTheory.QuadChirp.conj_coord_hasTemperateGrowth {m n : ℕ} (l : Fin m) (i : Fin n) :
    Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => star (u l i)) := by sorry
