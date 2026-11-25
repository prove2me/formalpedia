-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exact_coinvariantsMap
-- name    : GroundTheory.Automorphic.exact_coinvariantsMap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:13:15.332532+00:00
-- url     : https://prove2.me/theorems/e354e0b3-b866-4e04-9a5d-4c391fb6de79
-- title:
--   Automorphic: exact coinvariants Map
-- statement:
--   The Automorphic construction uses the exact coinvariants Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionJacquet.lean#L46-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionJacquet.lean#L46-L73

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
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
variable {N : Type*} [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
  [LocallyCompactSpace N] [T2Space N] [TotallyDisconnectedSpace N]
  {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ N V)
variable {W X : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]
  {ρ} {σ : Representation ℂ N W} {τ : Representation ℂ N X}

theorem GroundTheory.Automorphic.exact_coinvariantsMap
    (hN : ∀ s : Finset N, ∃ K : Subgroup N, IsCompact (K : Set N) ∧ IsOpen (K : Set N) ∧
      ∀ x ∈ s, x ∈ K)
    (hσ : IsSmooth σ) (hτ : IsSmooth τ)
    (f : Representation.IntertwiningMap ρ σ) (g : Representation.IntertwiningMap σ τ)
    (hfg : Function.Exact f g) :
    Function.Exact (Representation.Coinvariants.map ρ σ f)
      (Representation.Coinvariants.map σ τ g) := by sorry
