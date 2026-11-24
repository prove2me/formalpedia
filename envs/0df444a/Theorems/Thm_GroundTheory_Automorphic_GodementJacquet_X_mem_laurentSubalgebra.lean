-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_X_mem_laurentSubalgebra
-- name    : GroundTheory.Automorphic.GodementJacquet.X_mem_laurentSubalgebra
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:13.072189+00:00
-- url     : https://prove2.me/theorems/38287564-0454-4999-8364-116d554fdaa4
-- title:
--   Godement Jacquet: X mem laurent Subalgebra
-- statement:
--   The Godement Jacquet construction uses the X mem laurent Subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJLaurentIdeal.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJLaurentIdeal.lean#L15-L16

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

theorem GroundTheory.Automorphic.GodementJacquet.X_mem_laurentSubalgebra : (RatFunc.X : RatFunc ℂ) ∈ laurentSubalgebra := by sorry
