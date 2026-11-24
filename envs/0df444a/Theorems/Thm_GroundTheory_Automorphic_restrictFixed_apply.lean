-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_restrictFixed_apply
-- name    : GroundTheory.Automorphic.restrictFixed_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:28.540431+00:00
-- url     : https://prove2.me/theorems/e75a2459-044d-451f-81b4-50654b2bb87d
-- title:
--   Automorphic: restrict Fixed apply
-- statement:
--   The Automorphic construction uses the restrict Fixed apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepContragredient.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepContragredient.lean#L66-L69

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
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
open Set Filter Topology
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V)
variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem GroundTheory.Automorphic.restrictFixed_apply (H : Subgroup G) (x : fixedVectors (contragredient ρ) H)
    (v : fixedVectors ρ H) :
    restrictFixed ρ H x v =
      ((x : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) v := by sorry
