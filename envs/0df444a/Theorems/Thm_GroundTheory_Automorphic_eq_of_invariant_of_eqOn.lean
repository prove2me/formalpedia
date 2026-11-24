-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_eq_of_invariant_of_eqOn
-- name    : GroundTheory.Automorphic.eq_of_invariant_of_eqOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:28.270794+00:00
-- url     : https://prove2.me/theorems/c468a067-0a19-4057-8d59-3279f91ba82d
-- title:
--   Automorphic: eq of invariant of eq On
-- statement:
--   The Automorphic construction uses the eq of invariant of eq On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L369-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L369-L378

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StabilizerOf
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
variable {ρ} {K : Subgroup G}
variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
include hρ hKc hKo

theorem GroundTheory.Automorphic.eq_of_invariant_of_eqOn {W : Type*} [AddCommGroup W] [Module ℂ W] {f g : V →ₗ[ℂ] W}
    (hf : ∀ k ∈ K, ∀ v, f (ρ k v) = f v) (hg : ∀ k ∈ K, ∀ v, g (ρ k v) = g v)
    (h : ∀ v ∈ fixedVectors ρ K, f v = g v) : f = g := by sorry
