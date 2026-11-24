-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_doubleCosetMap_mk
-- name    : GroundTheory.GroupCoh.doubleCosetMap_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:11.530877+00:00
-- url     : https://prove2.me/theorems/64424759-4ea2-4065-94c1-63efc63d60e2
-- title:
--   Group Coh: double Coset Map mk
-- statement:
--   The Group Coh construction uses the double Coset Map mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DoubleCosetSum.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DoubleCosetSum.lean#L32-L34

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DoubleCosetSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Pointwise
open GroundTheory GroundTheory.GroupCoh
variable {G : Type*} [Group G] (T S : Subgroup G)

theorem GroundTheory.GroupCoh.doubleCosetMap_mk (g : G) (t : T) :
    doubleCosetMap T S g (t : T ⧸ (T ⊓ MulAut.conj g • S).subgroupOf T) = ((t * g : G) : G ⧸ S) := by sorry

attribute [defeq] GroundTheory.GroupCoh.doubleCosetMap_mk
