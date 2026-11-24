-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_coinvariantsKer_le_ker_of_invariant
-- name    : GroundTheory.Automorphic.coinvariantsKer_le_ker_of_invariant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:32.047733+00:00
-- url     : https://prove2.me/theorems/ff24175c-6273-4f07-a45a-da50a7afd67f
-- title:
--   Automorphic: coinvariants Ker le ker of invariant
-- statement:
--   The Automorphic construction uses the coinvariants Ker le ker of invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L70-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L70-L75

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
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V)
variable {ρ}

theorem GroundTheory.Automorphic.coinvariantsKer_le_ker_of_invariant {W : Type*} [AddCommGroup W] [Module ℂ W]
    {K : Subgroup G} {f : V →ₗ[ℂ] W} (hf : ∀ k ∈ K, ∀ v, f (ρ k v) = f v) :
    coinvariantsKer ρ K ≤ LinearMap.ker f := by sorry
