-- Prove2me | Theorems.Thm_GlobalTheory_JR_OKCompact_coeff_charpoly_lmul_smul
-- name    : GlobalTheory.JR.OKCompact.coeff_charpoly_lmul_smul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:34:30.401797+00:00
-- url     : https://prove2.me/theorems/52146923-e0f7-41f8-891b-8c9edb198e77
-- title:
--   OKCompact: coeff charpoly lmul smul
-- statement:
--   The OKCompact construction uses the coeff charpoly lmul smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCompactFiniteEtaleHermitianPairOK.lean#L35-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCompactFiniteEtaleHermitianPairOK.lean#L35-L41

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

theorem GlobalTheory.JR.OKCompact.coeff_charpoly_lmul_smul [Infinite F] (z : K) {c : F} (hc : c ≠ 0) (k : ℕ) :
    (LinearMap.charpoly (Algebra.lmul F K (c • z))).coeff k =
      (LinearMap.charpoly (Algebra.lmul F K z)).coeff k * c ^ (Module.finrank F K - k) := by sorry
