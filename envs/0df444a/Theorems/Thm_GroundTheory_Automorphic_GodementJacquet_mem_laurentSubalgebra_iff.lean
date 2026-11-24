-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_mem_laurentSubalgebra_iff
-- name    : GroundTheory.Automorphic.GodementJacquet.mem_laurentSubalgebra_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:43.692503+00:00
-- url     : https://prove2.me/theorems/2c80f421-3d34-461e-9712-d78cd6031a5b
-- title:
--   Godement Jacquet: mem laurent Subalgebra iff
-- statement:
--   The Godement Jacquet construction uses the mem laurent Subalgebra iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJLaurentIdeal.lean#L35-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJLaurentIdeal.lean#L35-L64

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

theorem GroundTheory.Automorphic.GodementJacquet.mem_laurentSubalgebra_iff {R : RatFunc ℂ} :
    R ∈ laurentSubalgebra ↔
      ∃ (P : ℂ[X]) (k : ℕ), R = algebraMap ℂ[X] (RatFunc ℂ) P / RatFunc.X ^ k := by sorry
