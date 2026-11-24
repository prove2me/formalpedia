-- Prove2me | Theorems.Thm_GlobalTheory_JR_et_equiv_continuous
-- name    : GlobalTheory.JR.et_equiv_continuous
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:38:18.219783+00:00
-- url     : https://prove2.me/theorems/bb916eaf-f0c7-4217-9462-2b90290ea5ee
-- title:
--   JR: et equiv continuous
-- statement:
--   The JR construction uses the et equiv continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteEtaleHermitianLinearEquivContinuous.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteEtaleHermitianLinearEquivContinuous.lean#L7-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteEtaleHermitianLinearEquivContinuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR

theorem GlobalTheory.JR.et_equiv_continuous (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)) :
    Continuous j ∧ Continuous j.symm := by sorry
