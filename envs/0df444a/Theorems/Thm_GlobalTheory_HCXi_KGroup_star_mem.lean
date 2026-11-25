-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_KGroup_star_mem
-- name    : GlobalTheory.HCXi.KGroup.star_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:49:31.705457+00:00
-- url     : https://prove2.me/theorems/55f23a04-7ac3-5dec-abf1-584ba4b65b5f
-- title:
--   KGroup: star mem
-- statement:
--   The KGroup construction uses the star mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MaximalCompactSubgroupProperties.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MaximalCompactSubgroupProperties.lean#L45-L47

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

theorem GlobalTheory.HCXi.KGroup.star_mem {k r : ℕ} {κ : Mat k r} (h : κ ∈ Kset k r) : κᴴ ∈ Kset k r := by sorry
