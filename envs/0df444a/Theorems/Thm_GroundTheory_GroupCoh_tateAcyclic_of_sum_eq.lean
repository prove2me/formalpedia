-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_of_sum_eq
-- name    : GroundTheory.GroupCoh.tateAcyclic_of_sum_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:23.975829+00:00
-- url     : https://prove2.me/theorems/25571e84-4639-467b-9289-5dbcbf1ab3cc
-- title:
--   Group Coh: tate Acyclic of sum eq
-- statement:
--   The Group Coh construction uses the tate Acyclic of sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InducedNorm.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InducedNorm.lean#L51-L53

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep MonoidalCategory
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
variable (M : Rep.{u} k G)

theorem GroundTheory.GroupCoh.tateAcyclic_of_sum_eq (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) : TateAcyclic M := by sorry
