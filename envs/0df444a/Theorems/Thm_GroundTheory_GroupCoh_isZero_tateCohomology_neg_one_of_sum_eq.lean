-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_isZero_tateCohomology_neg_one_of_sum_eq
-- name    : GroundTheory.GroupCoh.isZero_tateCohomology_neg_one_of_sum_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:43:08.827816+00:00
-- url     : https://prove2.me/theorems/14acf89b-aa9e-43d3-8581-cdd24739d597
-- title:
--   Group Coh: is Zero tate Cohomology neg one of sum eq
-- statement:
--   The Group Coh construction uses the is Zero tate Cohomology neg one of sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/Induced.lean#L75-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/Induced.lean#L75-L86

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
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
open CategoryTheory Limits groupCohomology groupHomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem GroundTheory.GroupCoh.isZero_tateCohomology_neg_one_of_sum_eq (M : Rep.{u} k G) (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) :
    IsZero (tateCohomology M (-1)) := by sorry
