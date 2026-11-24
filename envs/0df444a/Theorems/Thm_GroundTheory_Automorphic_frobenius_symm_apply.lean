-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- name    : GroundTheory.Automorphic.frobenius_symm_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:24:12.700377+00:00
-- url     : https://prove2.me/theorems/50e55035-3951-486c-a7d2-f883b483a7a0
-- title:
--   Automorphic: frobenius symm apply
-- statement:
--   The Automorphic construction uses the frobenius symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Induction.lean#L204-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Induction.lean#L204-L206

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_Induction
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
open Set Filter Topology Pointwise
variable {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G)
  {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W)
variable [IsTopologicalGroup G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
variable {π}

theorem GroundTheory.Automorphic.frobenius_symm_apply (hπ : IsSmooth π)
    (φ : Representation.IntertwiningMap (π.comp H.subtype) σ) (v : V) (g : G) :
    ((frobenius H σ hπ).symm φ v : G → W) g = φ (π g v) := by sorry

attribute [defeq] GroundTheory.Automorphic.frobenius_symm_apply
