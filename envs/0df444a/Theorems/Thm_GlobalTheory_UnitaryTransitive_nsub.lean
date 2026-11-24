-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryTransitive_nsub
-- name    : GlobalTheory.UnitaryTransitive.nsub
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:46:00.763013+00:00
-- url     : https://prove2.me/theorems/04bcb541-0f25-4362-84a3-e7c5de02d4f2
-- title:
--   Unitary Transitive: nsub
-- statement:
--   The Unitary Transitive construction uses the nsub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralUnitaryGroupTransitiveNormOneVectors.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralUnitaryGroupTransitiveNormOneVectors.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralUnitaryGroupTransitiveNormOneVectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.UnitaryTransitive
variable {E : Type} [NormedField E] [StarRing E]

theorem GlobalTheory.UnitaryTransitive.nsub [IsUltrametricDist E] (a b : E) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by sorry
