-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KerVec_tst_mul_right
-- name    : GlobalTheory.CompanionTheory.KerVec.tst_mul_right
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:50:52.457158+00:00
-- url     : https://prove2.me/theorems/725162e1-c580-4ce4-9bf4-2b1977d7f818
-- title:
--   Ker Vec: tst mul right
-- statement:
--   The Ker Vec construction uses the tst mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousAtOfSqBound.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousAtOfSqBound.lean#L16-L18

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousAtOfSqBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KerVec

theorem GlobalTheory.CompanionTheory.KerVec.tst_mul_right {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {φ : G → ℂ} (h : Tst φ) (w : G) : Tst (fun g => φ (g * w)) := by sorry
