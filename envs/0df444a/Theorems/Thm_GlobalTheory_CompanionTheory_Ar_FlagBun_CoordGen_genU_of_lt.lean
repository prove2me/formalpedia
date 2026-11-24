-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_genU_of_lt
-- name    : GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.genU_of_lt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:18:14.182117+00:00
-- url     : https://prove2.me/theorems/9fcc57f7-71e6-4902-be23-db0c51b3f370
-- title:
--   Coord Gen: gen U of lt
-- statement:
--   The Coord Gen construction uses the gen U of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FrameMatrixChartRatios.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FrameMatrixChartRatios.lean#L51-L53

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

theorem GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.genU_of_lt (s : S) {l k : Fin (r s)} (h : l < k) : genU Ω r s l k = 0 := by sorry
