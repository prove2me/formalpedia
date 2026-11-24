-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_mem_of_genU_mem
-- name    : GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.mem_of_genU_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:18:11.088472+00:00
-- url     : https://prove2.me/theorems/ffef18e1-543b-4635-a3a2-74f43950c736
-- title:
--   Coord Gen: mem of gen U mem
-- statement:
--   The Coord Gen construction uses the mem of gen U mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FrameMatrixChartRatios.lean#L157-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FrameMatrixChartRatios.lean#L157-L174

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

theorem GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.mem_of_genU_mem (L : Subfield (GenField Ω r)) (hbase : ∀ b : Ω, algebraMap Ω (GenField Ω r) b ∈ L)
    (hentry : ∀ (s : S) (k l : Fin (r s)), k ≤ l → genU Ω r s l k ∈ L) (a : GenField Ω r) : a ∈ L := by sorry
