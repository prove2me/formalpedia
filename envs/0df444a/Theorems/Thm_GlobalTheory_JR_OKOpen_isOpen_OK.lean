-- Prove2me | Theorems.Thm_GlobalTheory_JR_OKOpen_isOpen_OK
-- name    : GlobalTheory.JR.OKOpen.isOpen_OK
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:34:39.505471+00:00
-- url     : https://prove2.me/theorems/5b36c0e8-a7ef-4f3c-a926-8e0fcb3fb410
-- title:
--   OKOpen: is Open OK
-- statement:
--   The OKOpen construction uses the is Open OK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsOpenFiniteEtaleHermitianPairOK.lean#L34-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsOpenFiniteEtaleHermitianPairOK.lean#L34-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsOpenFiniteEtaleHermitianPairOK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OKOpen

theorem GlobalTheory.JR.OKOpen.isOpen_OK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E), IsOpen A.OK := by sorry
