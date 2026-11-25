-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_inv_eq_self_GL
-- name    : GroundTheory.Automorphic.Measures.inv_eq_self_GL
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:55:01.999843+00:00
-- url     : https://prove2.me/theorems/9157cdea-3501-444e-a538-a42dbfe9a1fb
-- title:
--   Measures: inv eq self GL
-- statement:
--   The Measures construction uses the inv eq self GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresGL.lean#L187-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresGL.lean#L187-L203

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel DoubleCoset
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)

theorem GroundTheory.Automorphic.Measures.inv_eq_self_GL [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] : μ.inv = μ := by sorry
