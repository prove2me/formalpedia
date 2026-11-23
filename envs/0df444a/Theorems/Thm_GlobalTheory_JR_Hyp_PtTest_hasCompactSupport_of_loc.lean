-- Prove2me | Theorems.Thm_GlobalTheory_JR_Hyp_PtTest_hasCompactSupport_of_loc
-- name    : GlobalTheory.JR.Hyp.PtTest.hasCompactSupport_of_loc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:34.607186+00:00
-- url     : https://prove2.me/theorems/fdb73618-375c-46d2-a071-37f3fe84728d
-- title:
--   Pt Test: has Compact Support of loc
-- statement:
--   The Pt Test construction uses the has Compact Support of loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PartialFourierPsiKPreservesTestFunctions.lean#L8-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PartialFourierPsiKPreservesTestFunctions.lean#L8-L18

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

theorem GlobalTheory.JR.Hyp.PtTest.hasCompactSupport_of_loc {X : Type} [TopologicalSpace X] (g : X → ℂ) (hg : IsLocallyConstant g)
    (C : Set X) (hC : IsCompact C) (hz : ∀ x ∉ C, g x = 0) : HasCompactSupport g := by sorry
