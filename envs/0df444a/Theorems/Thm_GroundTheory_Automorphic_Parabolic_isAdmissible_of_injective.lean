-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isAdmissible_of_injective
-- name    : GroundTheory.Automorphic.Parabolic.isAdmissible_of_injective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:21:33.57058+00:00
-- url     : https://prove2.me/theorems/611e5dd6-1acd-47d7-9f98-262129bfc740
-- title:
--   Parabolic: is Admissible of injective
-- statement:
--   The Parabolic construction uses the is Admissible of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdmissibleInduction.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdmissibleInduction.lean#L21-L25

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {V' : Type*} [AddCommGroup V'] [Module ℂ V'] {ρ' : Representation ℂ G V'}
omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

theorem GroundTheory.Automorphic.Parabolic.isAdmissible_of_injective (hρ : IsSmooth ρ) (hρ' : IsAdmissible ρ')
    (f : Representation.IntertwiningMap ρ ρ') (hf : Function.Injective f) : IsAdmissible ρ := by sorry
