-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadricUnit_card_quadric_unit
-- name    : GlobalTheory.CompanionTheory.SW.QuadricUnit.card_quadric_unit
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:07:50.20151+00:00
-- url     : https://prove2.me/theorems/f8cd3a07-877b-4fd2-90c7-7b19c4045ced
-- title:
--   Quadric Unit: card quadric unit
-- statement:
--   The Quadric Unit construction uses the card quadric unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardQuadricUnit.lean#L132-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardQuadricUnit.lean#L132-L190

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

theorem GlobalTheory.CompanionTheory.SW.QuadricUnit.card_quadric_unit (hchar : ringChar k ≠ 2) (M : ℕ) (hM : Fintype.card ι = 2 * M)
    (hM1 : 1 ≤ M) (B : Matrix ι ι k) (hB : B.IsSymm) (hdet : B.det ≠ 0) {s : k} (hs : s ≠ 0) :
    |(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) -
      (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤ (Fintype.card k : ℝ) ^ (M - 1) := by sorry
