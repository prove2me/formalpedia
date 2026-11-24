-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_mem_coinvariantsKer
-- name    : GroundTheory.Automorphic.exists_mem_coinvariantsKer
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:43:11.645706+00:00
-- url     : https://prove2.me/theorems/74d24416-d23a-498a-aa67-d0dd358fd439
-- title:
--   Automorphic: exists mem coinvariants Ker
-- statement:
--   The Automorphic construction uses the exists mem coinvariants Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionJacquet.lean#L27-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionJacquet.lean#L27-L41

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
omit [IsTopologicalGroup N] [LocallyCompactSpace N] [T2Space N] [TotallyDisconnectedSpace N]

theorem GroundTheory.Automorphic.exists_mem_coinvariantsKer
    (hN : ∀ s : Finset N, ∃ K : Subgroup N, IsCompact (K : Set N) ∧ IsOpen (K : Set N) ∧
      ∀ x ∈ s, x ∈ K)
    {v : V} (hv : v ∈ Representation.Coinvariants.ker ρ) :
    ∃ K : Subgroup N, IsCompact (K : Set N) ∧ IsOpen (K : Set N) ∧ v ∈ coinvariantsKer ρ K := by sorry
