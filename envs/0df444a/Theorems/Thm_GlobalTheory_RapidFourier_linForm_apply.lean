-- Prove2me | Theorems.Thm_GlobalTheory_RapidFourier_linForm_apply
-- name    : GlobalTheory.RapidFourier.linForm_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:30.48582+00:00
-- url     : https://prove2.me/theorems/e1132df5-5370-434d-a99e-6c5b1ccefb95
-- title:
--   Rapid Fourier: lin Form apply
-- statement:
--   The Rapid Fourier construction uses the lin Form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ContDiffAndFderivTsumFourierOfRapid.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ContDiffAndFderivTsumFourierOfRapid.lean#L13-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
open GlobalTheory.RapidFourier

theorem GlobalTheory.RapidFourier.linForm_apply {n : ℕ} (ν : Fin n → ℤ) (x : Fin n → ℝ) :
    linForm ν x = ∑ k, (ν k : ℝ) * x k := by sorry
