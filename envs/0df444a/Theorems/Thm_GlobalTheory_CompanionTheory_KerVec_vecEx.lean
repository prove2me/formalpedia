-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KerVec_vecEx
-- name    : GlobalTheory.CompanionTheory.KerVec.vecEx
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:49.118824+00:00
-- url     : https://prove2.me/theorems/99281a71-37ee-4d38-bef6-05ba46ca4927
-- title:
--   Ker Vec: vec Ex
-- statement:
--   The Ker Vec construction uses the vec Ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousAtOfSqBound.lean#L45-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousAtOfSqBound.lean#L45-L77

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

theorem GlobalTheory.CompanionTheory.KerVec.vecEx : CntBasic → KernelL2RowsColumns → TwoUnif → VecClose → VecEx := by sorry
