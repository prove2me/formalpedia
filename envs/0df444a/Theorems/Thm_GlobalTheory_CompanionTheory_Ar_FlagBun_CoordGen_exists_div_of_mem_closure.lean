-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_exists_div_of_mem_closure
-- name    : GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.exists_div_of_mem_closure
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:17:57.277742+00:00
-- url     : https://prove2.me/theorems/e2ba90bc-0aaa-48bd-a75b-6e66ee64c673
-- title:
--   Coord Gen: exists div of mem closure
-- statement:
--   The Coord Gen construction uses the exists div of mem closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FrameMatrixChartRatios.lean#L33-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FrameMatrixChartRatios.lean#L33-L47

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

theorem GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.exists_div_of_mem_closure {K : Type*} [Field K] [Algebra ℤ K] {t : Set K} {a : K} (ha : a ∈ Subfield.closure t) :
    ∃ g ∈ Algebra.adjoin ℤ t, ∃ h ∈ Algebra.adjoin ℤ t, h ≠ 0 ∧ a = g / h := by sorry
