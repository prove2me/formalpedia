-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadricUnit_sum_sq_eq
-- name    : GlobalTheory.CompanionTheory.SW.QuadricUnit.sum_sq_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:10:22.708683+00:00
-- url     : https://prove2.me/theorems/104e624b-77d1-4074-a274-b059088d5859
-- title:
--   Quadric Unit: sum sq eq
-- statement:
--   The Quadric Unit construction uses the sum sq eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardQuadricUnit.lean#L20-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardQuadricUnit.lean#L20-L44

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteFieldQuadraticFormPointCount
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardQuadricUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadricUnit
open GlobalTheory.CompanionTheory.SW.QuadricCount
variable {k : Type} [Field k] [Fintype k] [DecidableEq k]

theorem GlobalTheory.CompanionTheory.SW.QuadricUnit.sum_sq_eq (hchar : ringChar k ≠ 2) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) {c : k} (hc : c ≠ 0) :
    ∑ y : k, ψ (c * (y * y)) = ∑ z : k, (quadraticChar k z : ℂ) * ψ (c * z) := by sorry
