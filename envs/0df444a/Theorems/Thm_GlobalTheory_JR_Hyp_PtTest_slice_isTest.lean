-- Prove2me | Theorems.Thm_GlobalTheory_JR_Hyp_PtTest_slice_isTest
-- name    : GlobalTheory.JR.Hyp.PtTest.slice_isTest
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:33:30.63872+00:00
-- url     : https://prove2.me/theorems/d2951907-179b-4290-8f10-d47e5d23f617
-- title:
--   Pt Test: slice is Test
-- statement:
--   The Pt Test construction uses the slice is Test property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PartialFourierPsiKPreservesTestFunctions.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PartialFourierPsiKPreservesTestFunctions.lean#L40-L46

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierPsiKPreservesTestFunctions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Hyp GlobalTheory.JR.Hyp.PtTest

theorem GlobalTheory.JR.Hyp.PtTest.slice_isTest {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (Φ : X × Y → ℂ) (hΦ : IsTest Φ)
    (a : X) : IsTest fun b => Φ (a, b) := by sorry
