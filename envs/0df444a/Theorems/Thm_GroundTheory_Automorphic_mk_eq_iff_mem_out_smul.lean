-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mk_eq_iff_mem_out_smul
-- name    : GroundTheory.Automorphic.mk_eq_iff_mem_out_smul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:36:05.74105+00:00
-- url     : https://prove2.me/theorems/d8c31aa3-b009-486d-94d7-bbe3be6e0714
-- title:
--   Automorphic: mk eq iff mem out smul
-- statement:
--   The Automorphic construction uses the mk eq iff mem out smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyConstantCompact.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyConstantCompact.lean#L61-L64

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
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
open scoped Pointwise
variable {G : Type*} [Group G] {E : Type*}

theorem GroundTheory.Automorphic.mk_eq_iff_mem_out_smul (K : Subgroup G) (x : G ⧸ K) (y : G) :
    (y : G ⧸ K) = x ↔ y ∈ x.out • (K : Set G) := by sorry
