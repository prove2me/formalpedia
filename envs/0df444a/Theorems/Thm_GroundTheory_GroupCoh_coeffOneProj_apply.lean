-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_coeffOneProj_apply
-- name    : GroundTheory.GroupCoh.coeffOneProj_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:00.352799+00:00
-- url     : https://prove2.me/theorems/3ec0f439-4f64-4e70-942e-8ddf4368c826
-- title:
--   Group Coh: coeff One Proj apply
-- statement:
--   The Group Coh construction uses the coeff One Proj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InducedNorm.lean#L66-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InducedNorm.lean#L66-L67

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
omit [Fintype G]

theorem GroundTheory.GroupCoh.coeffOneProj_apply (x : MonoidAlgebra k G) :
    coeffOneProj x = MonoidAlgebra.single 1 (x.coeff 1) := by sorry
