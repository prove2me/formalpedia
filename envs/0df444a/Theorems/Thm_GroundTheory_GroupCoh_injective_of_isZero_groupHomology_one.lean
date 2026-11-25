-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_injective_of_isZero_groupHomology_one
-- name    : GroundTheory.GroupCoh.injective_of_isZero_groupHomology_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:43:29.930978+00:00
-- url     : https://prove2.me/theorems/d05040de-85b9-4fef-8564-1afbc2f97849
-- title:
--   Group Coh: injective of is Zero group Homology one
-- statement:
--   The Group Coh construction uses the injective of is Zero group Homology one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupFree.lean#L91-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupFree.lean#L91-L122

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_TateAddEquivAbelianizationTateClass
import Definitions.Def_GroundTheory_TateCohomology_PGroupFixed
import Definitions.Def_GroundTheory_TateCohomology_PGroupFree
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
open CategoryTheory Limits groupHomology Representation Finsupp
open scoped MonoidAlgebra
universe u
variable {k G : Type u} [Field k] [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]

theorem GroundTheory.GroupCoh.injective_of_isZero_groupHomology_one (hG : IsPGroup p G) {A B : Rep.{u} k G} (f : A ⟶ B)
    (hsurj : Function.Surjective f.hom) (hB : IsZero (groupHomology B 1))
    (hker : ∀ x, f.hom x = 0 → x ∈ Coinvariants.ker A.ρ) : Function.Injective f.hom := by sorry
