-- Prove2me | Theorems.Thm_GlobalTheory_RankStrata_Nsp_le_SB
-- name    : GlobalTheory.RankStrata.Nsp_le_SB
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:14:53.803853+00:00
-- url     : https://prove2.me/theorems/b48e4380-37ed-4858-95e0-1c7a37511cc7
-- title:
--   Rank Strata: Nsp le SB
-- statement:
--   The Rank Strata construction uses the Nsp le SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubMemNsp.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubMemNsp.lean#L18-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix
noncomputable section
open GlobalTheory GlobalTheory.RankStrata
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}

theorem GlobalTheory.RankStrata.Nsp_le_SB (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν : kˣ →* ℂˣ) :
    Nsp k A D ν ≤ SB (Matrix A D k) := by sorry
