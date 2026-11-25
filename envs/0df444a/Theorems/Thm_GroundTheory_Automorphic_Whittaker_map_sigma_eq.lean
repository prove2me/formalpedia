-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_map_sigma_eq
-- name    : GroundTheory.Automorphic.Whittaker.map_sigma_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:07:22.161887+00:00
-- url     : https://prove2.me/theorems/22244b8e-9ac5-5477-b152-e64733748c9f
-- title:
--   Whittaker: map sigma eq
-- statement:
--   The Whittaker construction uses the map sigma eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLocal.lean#L42-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLocal.lean#L42-L74

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open MeasureTheory Measure ValuativeRel
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]

theorem GroundTheory.Automorphic.Whittaker.map_sigma_eq (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] : μ.map sigma = μ := by sorry
