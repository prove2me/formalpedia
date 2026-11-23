-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_transvectionGL_mem_elementarySubgroup
-- name    : GroundTheory.Automorphic.transvectionGL_mem_elementarySubgroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:24.964799+00:00
-- url     : https://prove2.me/theorems/2a6b7e5c-fee0-4824-86f0-915003ccbfa1
-- title:
--   Automorphic: transvection GL mem elementary Subgroup
-- statement:
--   The Automorphic construction uses the transvection GL mem elementary Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StrongApproximationSLElementary.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StrongApproximationSLElementary.lean#L28-L30

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StrongApproximationSLElementary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GroundTheory GroundTheory.Automorphic
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (n) (R : Type*) [CommRing R]
variable {n R}

theorem GroundTheory.Automorphic.transvectionGL_mem_elementarySubgroup (t : TransvectionStruct n R) :
    transvectionGL n R t ∈ elementarySubgroup n R := by sorry
