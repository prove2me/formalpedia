-- Prove2me | Theorems.Thm_GlobalTheory_JR_OKOpen_continuous_coeff
-- name    : GlobalTheory.JR.OKOpen.continuous_coeff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:34:39.339655+00:00
-- url     : https://prove2.me/theorems/f194fecd-0116-427f-a15e-dc898b82c139
-- title:
--   OKOpen: continuous coeff
-- statement:
--   The OKOpen construction uses the continuous coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsOpenFiniteEtaleHermitianPairOK.lean#L18-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsOpenFiniteEtaleHermitianPairOK.lean#L18-L32

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

theorem GlobalTheory.JR.OKOpen.continuous_coeff {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E) (i : ℕ) :
    Continuous fun z : A.K => (LinearMap.charpoly (Algebra.lmul F A.K z)).coeff i := by sorry
