-- Prove2me | Theorems.Thm_GlobalTheory_finiteNormedAlgebra_eq_moduleTopology
-- name    : GlobalTheory.finiteNormedAlgebra_eq_moduleTopology
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:44.02182+00:00
-- url     : https://prove2.me/theorems/87be6b1b-7e47-47af-9c28-82e9a5e701cd
-- title:
--   Global Theory: finite Normed Algebra eq module Topology
-- statement:
--   The Global Theory construction uses the finite Normed Algebra eq module Topology property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteNormedAlgebraEqModuleTopology.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteNormedAlgebraEqModuleTopology.lean#L33-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open GlobalTheory
open MeasureTheory Filter Topology

theorem GlobalTheory.finiteNormedAlgebra_eq_moduleTopology (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] (R : Type) [N : NormedCommRing R] [NormedAlgebra F R]
    [Module.Finite F R] :
    N.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      = moduleTopology F R := by sorry
