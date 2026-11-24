-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KerPoint_eq_zero_of_le_small
-- name    : GlobalTheory.CompanionTheory.KerPoint.eq_zero_of_le_small
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:50:41.745092+00:00
-- url     : https://prove2.me/theorems/dc94bf7b-fbcc-4971-9cb7-820d1dcd5c69
-- title:
--   Ker Point: eq zero of le small
-- statement:
--   The Ker Point construction uses the eq zero of le small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EqZeroOfLeSmall.lean#L57-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EqZeroOfLeSmall.lean#L57-L66

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EqZeroOfLeSmall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KerPoint

theorem GlobalTheory.CompanionTheory.KerPoint.eq_zero_of_le_small {D C : ℝ} (hC : 0 ≤ C) (h : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → D ≤ δ * C) : D ≤ 0 := by sorry
