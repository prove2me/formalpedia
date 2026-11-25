-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_Funct_gv_mul
-- name    : GlobalTheory.HCXi.Funct.gv_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:53:59.588122+00:00
-- url     : https://prove2.me/theorems/b356898d-03f6-5a9e-ad20-dcf1341f849e
-- title:
--   Funct: gv mul
-- statement:
--   The Funct construction uses the gv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SphericalFunctionFunctionalEq.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SphericalFunctionFunctionalEq.lean#L12-L19

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

theorem GlobalTheory.HCXi.Funct.gv_mul {k r : ℕ} {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r) : a * b ∈ GV k r := by sorry
