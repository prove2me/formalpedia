-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_biTranslL_eq
-- name    : GroundTheory.Automorphic.Whittaker.biTranslL_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:06:25.863035+00:00
-- url     : https://prove2.me/theorems/598468ca-bd8f-42ba-aa0d-2f7bacbefba3
-- title:
--   Whittaker: bi Transl L eq
-- statement:
--   The Whittaker construction uses the bi Transl L eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L66-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L66-L68

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Filter Topology MeasureTheory
variable {X : Type*} [TopologicalSpace X]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem GroundTheory.Automorphic.Whittaker.biTranslL_eq (a b : G) (f : locallyConstantCompactSupport G ℂ ℂ) :
    biTranslL a b f = ltransL a (rtransL b f) := by sorry
