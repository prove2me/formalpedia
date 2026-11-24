-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadricUnit_sum_sq_scale
-- name    : GlobalTheory.CompanionTheory.SW.QuadricUnit.sum_sq_scale
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:09:15.49819+00:00
-- url     : https://prove2.me/theorems/e613a6b3-d69b-47a6-948c-d902eb8282db
-- title:
--   Quadric Unit: sum sq scale
-- statement:
--   The Quadric Unit construction uses the sum sq scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardQuadricUnit.lean#L46-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardQuadricUnit.lean#L46-L57

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

theorem GlobalTheory.CompanionTheory.SW.QuadricUnit.sum_sq_scale (hchar : ringChar k ≠ 2) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) {c t : k}
    (hc : c ≠ 0) (ht : t ≠ 0) :
    ∑ y : k, ψ ((t * c) * (y * y)) = (quadraticChar k t : ℂ) * ∑ y : k, ψ (c * (y * y)) := by sorry
