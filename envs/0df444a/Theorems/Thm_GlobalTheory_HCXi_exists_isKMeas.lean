-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_exists_isKMeas
-- name    : GlobalTheory.HCXi.exists_isKMeas
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:48:43.480929+00:00
-- url     : https://prove2.me/theorems/19b82d88-e4c0-550c-abea-5e26a9e91222
-- title:
--   HCXi: exists is KMeas
-- statement:
--   The HCXi construction uses the exists is KMeas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsCompactHaarMeasure.lean#L10-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsCompactHaarMeasure.lean#L10-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MaximalCompactSubgroupPropertiesStatement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsCompactHaarMeasure
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
open GlobalTheory GlobalTheory.HCXi

theorem GlobalTheory.HCXi.exists_isKMeas : ∀ k r : ℕ, ∃ μK : Measure (Mt k r), IsKMeas k r μK := by sorry
