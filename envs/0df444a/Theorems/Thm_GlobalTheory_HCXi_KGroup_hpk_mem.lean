-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_KGroup_hpk_mem
-- name    : GlobalTheory.HCXi.KGroup.hpk_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:50:21.860104+00:00
-- url     : https://prove2.me/theorems/ffa8157f-4f31-4634-bd75-f0f4be53fbaf
-- title:
--   KGroup: hpk mem
-- statement:
--   The KGroup construction uses the hpk mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MaximalCompactSubgroupProperties.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MaximalCompactSubgroupProperties.lean#L39-L43

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

theorem GlobalTheory.HCXi.KGroup.hpk_mem (k r : ℕ) : Hpk k r ∈ Kset k r := by sorry
