-- Prove2me | Theorems.Thm_GlobalTheory_JR_OKCompact_continuous_coeff_lmul
-- name    : GlobalTheory.JR.OKCompact.continuous_coeff_lmul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:34:56.296791+00:00
-- url     : https://prove2.me/theorems/53e96b50-fc3e-4b8d-b7be-fc1a63b113a0
-- title:
--   OKCompact: continuous coeff lmul
-- statement:
--   The OKCompact construction uses the continuous coeff lmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCompactFiniteEtaleHermitianPairOK.lean#L43-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCompactFiniteEtaleHermitianPairOK.lean#L43-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCompactFiniteEtaleHermitianPairOK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OKCompact
variable {F : Type} [NontriviallyNormedField F] {K : Type} [CommRing K] [Algebra F K] [Module.Finite F K]

theorem GlobalTheory.JR.OKCompact.continuous_coeff_lmul [TopologicalSpace K] [IsModuleTopology F K] (k : ℕ) :
    Continuous fun z : K => (LinearMap.charpoly (Algebra.lmul F K z)).coeff k := by sorry
