-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_KGroup_sum_normSq_eq_trace
-- name    : GlobalTheory.HCXi.KGroup.sum_normSq_eq_trace
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:49:38.356082+00:00
-- url     : https://prove2.me/theorems/6c72768f-2522-5a71-a55b-2a891b902588
-- title:
--   KGroup: sum norm Sq eq trace
-- statement:
--   The KGroup construction uses the sum norm Sq eq trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MaximalCompactSubgroupProperties.lean#L56-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MaximalCompactSubgroupProperties.lean#L56-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MaximalCompactSubgroupProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.KGroup

theorem GlobalTheory.HCXi.KGroup.sum_normSq_eq_trace {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, ∑ j, Complex.normSq (g i j) = (trace (gᴴ * g)).re := by sorry
