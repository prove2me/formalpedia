-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KerPoint_ptEq_of
-- name    : GlobalTheory.CompanionTheory.KerPoint.ptEq_of
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:50:51.194981+00:00
-- url     : https://prove2.me/theorems/e4a87984-02d5-438f-9e69-d9f26f9a56ad
-- title:
--   Ker Point: pt Eq of
-- statement:
--   The Ker Point construction uses the pt Eq of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EqZeroOfLeSmall.lean#L68-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EqZeroOfLeSmall.lean#L68-L120

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

theorem GlobalTheory.CompanionTheory.KerPoint.ptEq_of : KerBasic → CvTest → OpAdj → ColOp → BumpEx → ApproxU → KerClose → VecLim → PtEq := by sorry
