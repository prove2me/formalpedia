-- Prove2me | Theorems.Thm_GlobalTheory_JR_SqrtNearOne_exists_sq_eq_inv_near_one
-- name    : GlobalTheory.JR.SqrtNearOne.exists_sq_eq_inv_near_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:35:33.043854+00:00
-- url     : https://prove2.me/theorems/89993272-6ad2-4d32-8bd3-de970c679d7f
-- title:
--   Sqrt Near One: exists sq eq inv near one
-- statement:
--   The Sqrt Near One construction uses the exists sq eq inv near one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteEtaleExistsSqRootNearOne.lean#L6-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteEtaleExistsSqRootNearOne.lean#L6-L55

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteEtaleExistsSqRootNearOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.SqrtNearOne

theorem GlobalTheory.JR.SqrtNearOne.exists_sq_eq_inv_near_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ∀ U ∈ 𝓝 (1 : A.K), ∀ᶠ v in 𝓝 (1 : A.K), ∃ s ∈ U, ∃ s' ∈ U, s * s' = 1 ∧ s ^ 2 = v := by sorry
