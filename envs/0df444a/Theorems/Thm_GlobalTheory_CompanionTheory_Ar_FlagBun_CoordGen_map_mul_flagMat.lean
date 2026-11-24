-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_map_mul_flagMat
-- name    : GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.map_mul_flagMat
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:18:27.704794+00:00
-- url     : https://prove2.me/theorems/b5147674-0253-403a-94dc-7bba55d4ae9c
-- title:
--   Coord Gen: map mul flag Mat
-- statement:
--   The Coord Gen construction uses the map mul flag Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FrameMatrixChartRatios.lean#L84-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FrameMatrixChartRatios.lean#L84-L93

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_CoordTieCompEquiv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_FrameMatrixChartRatios
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
variable {Ω : Type} [Field Ω] {S : Type} {r : S → ℕ}
variable {E : Type} [AddCommGroup E] [Module Ω E] {n : S → ℕ}

theorem GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.map_mul_flagMat (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (s : S)
    (B : Matrix (Fin (r s)) (Fin (n s)) Ω)
    (hB : B * Matrix.of (fun j l => φ s j (c s l)) = 1) :
    B.map (algebraMap Ω (GenField Ω r)) * flagMat φ c s = genU Ω r s := by sorry
