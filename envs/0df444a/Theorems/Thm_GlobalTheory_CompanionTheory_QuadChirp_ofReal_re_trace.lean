-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QuadChirp_ofReal_re_trace
-- name    : GlobalTheory.CompanionTheory.QuadChirp.ofReal_re_trace
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:56:19.695974+00:00
-- url     : https://prove2.me/theorems/469972d6-1789-4fdb-974e-4ef879638e4e
-- title:
--   Quad Chirp: of Real re trace
-- statement:
--   The Quad Chirp construction uses the of Real re trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SchwartzQuadraticPhaseMultiplication.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SchwartzQuadraticPhaseMultiplication.lean#L8-L15

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

theorem GlobalTheory.CompanionTheory.QuadChirp.ofReal_re_trace {m n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b)
    (A : Matrix (Fin m) (Fin n) ℂ) :
    (((Matrix.trace (b * (Aᴴ * A))).re : ℝ) : ℂ) = Matrix.trace (b * (Aᴴ * A)) := by sorry
