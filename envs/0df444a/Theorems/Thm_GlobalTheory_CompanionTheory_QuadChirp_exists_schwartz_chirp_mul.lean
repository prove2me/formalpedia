-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QuadChirp_exists_schwartz_chirp_mul
-- name    : GlobalTheory.CompanionTheory.QuadChirp.exists_schwartz_chirp_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:55:54.313971+00:00
-- url     : https://prove2.me/theorems/81cf747f-3d33-44ba-a989-34dd939822d6
-- title:
--   Quad Chirp: exists schwartz chirp mul
-- statement:
--   The Quad Chirp construction uses the exists schwartz chirp mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SchwartzQuadraticPhaseMultiplication.lean#L60-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SchwartzQuadraticPhaseMultiplication.lean#L60-L69

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

theorem GlobalTheory.CompanionTheory.QuadChirp.exists_schwartz_chirp_mul :
    ∀ (m n : ℕ) (k : ℝ) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b →
      ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ,
        ⇑ψ = fun u => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) *
          Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) * φ u := by sorry
