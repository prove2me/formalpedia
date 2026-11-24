-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_det_mul_eq_sum
-- name    : GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.det_mul_eq_sum
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:17:46.039957+00:00
-- url     : https://prove2.me/theorems/15667582-4561-44c3-8462-e033767ac95a
-- title:
--   Coord Gen: det mul eq sum
-- statement:
--   The Coord Gen construction uses the det mul eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FrameMatrixChartRatios.lean#L10-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FrameMatrixChartRatios.lean#L10-L23

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

theorem GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.det_mul_eq_sum {R : Type*} [CommRing R] {m p : Type*} [Fintype m] [DecidableEq m] [Fintype p]
    [DecidableEq p] (A : Matrix m p R) (C : Matrix p m R) :
    (A * C).det = ∑ f : m → p, (∏ i, A i (f i)) * (C.submatrix f id).det := by sorry
