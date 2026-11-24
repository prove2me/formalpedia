-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_C_mem_laurentSubalgebra
-- name    : GroundTheory.Automorphic.GodementJacquet.C_mem_laurentSubalgebra
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:56.337854+00:00
-- url     : https://prove2.me/theorems/9b7a748b-d08a-4f0d-8bf9-1c5f4cce89fa
-- title:
--   Godement Jacquet: C mem laurent Subalgebra
-- statement:
--   The Godement Jacquet construction uses the C mem laurent Subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJLaurentIdeal.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJLaurentIdeal.lean#L21-L23

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJLaurentIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Polynomial

theorem GroundTheory.Automorphic.GodementJacquet.C_mem_laurentSubalgebra (c : ℂ) : RatFunc.C c ∈ laurentSubalgebra := by sorry
