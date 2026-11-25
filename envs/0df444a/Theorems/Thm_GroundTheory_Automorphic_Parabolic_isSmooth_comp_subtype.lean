-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isSmooth_comp_subtype
-- name    : GroundTheory.Automorphic.Parabolic.isSmooth_comp_subtype
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:12:17.825844+00:00
-- url     : https://prove2.me/theorems/2bb8561f-0797-4d5a-85c6-91ab1996c6c6
-- title:
--   Parabolic: is Smooth comp subtype
-- statement:
--   The Parabolic construction uses the is Smooth comp subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolic.lean#L30-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolic.lean#L30-L39

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Induction
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
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
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal Topology Filter Set MeasureTheory Measure
open scoped NNReal

theorem GroundTheory.Automorphic.Parabolic.isSmooth_comp_subtype {G : Type*} [Group G] [TopologicalSpace G] {V : Type*}
    [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V} (hπ : IsSmooth π)
    (H : Subgroup G) : IsSmooth (π.comp H.subtype) := by sorry
