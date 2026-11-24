-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QuadChirp_coord_hasTemperateGrowth
-- name    : GlobalTheory.CompanionTheory.QuadChirp.coord_hasTemperateGrowth
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:56:02.253328+00:00
-- url     : https://prove2.me/theorems/9cb23ba5-d5bb-4085-af40-919fc137089a
-- title:
--   Quad Chirp: coord has Temperate Growth
-- statement:
--   The Quad Chirp construction uses the coord has Temperate Growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SchwartzQuadraticPhaseMultiplication.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SchwartzQuadraticPhaseMultiplication.lean#L17-L20

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

theorem GlobalTheory.CompanionTheory.QuadChirp.coord_hasTemperateGrowth {m n : ℕ} (l : Fin m) (i : Fin n) :
    Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => u l i) := by sorry
