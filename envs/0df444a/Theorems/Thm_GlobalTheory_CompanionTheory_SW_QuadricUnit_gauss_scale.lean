-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadricUnit_gauss_scale
-- name    : GlobalTheory.CompanionTheory.SW.QuadricUnit.gauss_scale
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:07:53.032795+00:00
-- url     : https://prove2.me/theorems/cdd22db6-a787-4ebc-a0a8-7c3d16ee1881
-- title:
--   Quadric Unit: gauss scale
-- statement:
--   The Quadric Unit construction uses the gauss scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardQuadricUnit.lean#L65-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardQuadricUnit.lean#L65-L130

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
variable {k : Type} [Field k] [Fintype k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.SW.QuadricUnit.gauss_scale (hchar : ringChar k ≠ 2) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    {B : Matrix ι ι k} (hB : B.IsSymm) (hdet : B.det ≠ 0) {M : ℕ}
    (hM : Fintype.card ι = 2 * M) {t : k} (ht : t ≠ 0) :
    ∑ x, ψ (t * quadForm B x) = ∑ x, ψ (quadForm B x) := by sorry
