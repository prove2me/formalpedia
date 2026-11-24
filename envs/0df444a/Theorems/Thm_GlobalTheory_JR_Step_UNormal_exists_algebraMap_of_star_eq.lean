-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_UNormal_exists_algebraMap_of_star_eq
-- name    : GlobalTheory.JR.Step.UNormal.exists_algebraMap_of_star_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:36:06.087861+00:00
-- url     : https://prove2.me/theorems/80e70551-853d-41a2-9bb8-e7699dd21f85
-- title:
--   UNormal: exists algebra Map of star eq
-- statement:
--   The UNormal construction uses the exists algebra Map of star eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryOrbitNormalFormUnitInvariant.lean#L14-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryOrbitNormalFormUnitInvariant.lean#L14-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjTransposeVecMulVecSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryOrbitNormalFormUnitInvariant
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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step GlobalTheory.JR.Step.UNormal
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
  [StarRing E] [Unram F E]

theorem GlobalTheory.JR.Step.UNormal.exists_algebraMap_of_star_eq (y : E) (hy : star y = y) : ∃ x : F, algebraMap F E x = y := by sorry
