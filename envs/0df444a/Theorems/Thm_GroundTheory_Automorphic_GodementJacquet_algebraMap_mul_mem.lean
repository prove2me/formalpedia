-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_algebraMap_mul_mem
-- name    : GroundTheory.Automorphic.GodementJacquet.algebraMap_mul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:08.527891+00:00
-- url     : https://prove2.me/theorems/e6d4a0d5-2752-4935-a094-f1b41fcecb4c
-- title:
--   Godement Jacquet: algebra Map mul mem
-- statement:
--   The Godement Jacquet construction uses the algebra Map mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJLaurentIdeal.lean#L148-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJLaurentIdeal.lean#L148-L164

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
variable {I : Submodule ℂ (RatFunc ℂ)}

theorem GroundTheory.Automorphic.GodementJacquet.algebraMap_mul_mem (hX : ∀ R ∈ I, RatFunc.X * R ∈ I) (P : ℂ[X]) {R : RatFunc ℂ}
    (hR : R ∈ I) : algebraMap ℂ[X] (RatFunc ℂ) P * R ∈ I := by sorry
