-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_Funct_cont_of
-- name    : GlobalTheory.HCXi.Funct.cont_of
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:09:46.643391+00:00
-- url     : https://prove2.me/theorems/df084332-d1eb-5da7-9387-d8ec253b9cf9
-- title:
--   Funct: cont of
-- statement:
--   The Funct construction uses the cont of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SphericalFunctionFunctionalEq.lean#L28-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SphericalFunctionFunctionalEq.lean#L28-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramPositiveVolumeContinuousStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_KsetTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeEquivariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SphericalFunctionFunctionalEq
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
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.Funct

theorem GlobalTheory.HCXi.Funct.cont_of {k r : ℕ} : Continuous fun κ : Mt k r => (Matrix.of κ : Mat k r) := by sorry
