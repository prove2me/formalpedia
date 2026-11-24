-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_det_genU_rows
-- name    : GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.det_genU_rows
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:31.816805+00:00
-- url     : https://prove2.me/theorems/29c6c450-bd21-442c-ac5c-1b5ca39b1b0d
-- title:
--   Coord Gen: det gen U rows
-- statement:
--   The Coord Gen construction uses the det gen U rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FrameMatrixChartRatios.lean#L58-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FrameMatrixChartRatios.lean#L58-L80

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

theorem GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.det_genU_rows (s : S) (k l : Fin (r s)) (hkl : k ≤ l) :
    ((genU Ω r s).submatrix
      (fun i : Fin ((k : ℕ) + 1) => if (i : ℕ) = k then l else Fin.castLE k.2 i) (Fin.castLE k.2)).det
      = genU Ω r s l k := by sorry
