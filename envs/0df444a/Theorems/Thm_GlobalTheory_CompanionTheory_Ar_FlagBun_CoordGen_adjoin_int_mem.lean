-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_adjoin_int_mem
-- name    : GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.adjoin_int_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:18:09.256134+00:00
-- url     : https://prove2.me/theorems/f931ada1-5635-4f6c-b05d-ea845361fcd2
-- title:
--   Coord Gen: adjoin int mem
-- statement:
--   The Coord Gen construction uses the adjoin int mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FrameMatrixChartRatios.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FrameMatrixChartRatios.lean#L25-L31

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

theorem GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.adjoin_int_mem {K : Type*} [Field K] (L : Subfield K) {t : Set K} (ht : ∀ a ∈ t, a ∈ L) {g : K}
    (hg : g ∈ Algebra.adjoin ℤ t) : g ∈ L := by sorry
