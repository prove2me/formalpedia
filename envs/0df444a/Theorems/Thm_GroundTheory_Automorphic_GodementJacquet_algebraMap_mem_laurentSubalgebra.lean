-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_algebraMap_mem_laurentSubalgebra
-- name    : GroundTheory.Automorphic.GodementJacquet.algebraMap_mem_laurentSubalgebra
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:30:03.769204+00:00
-- url     : https://prove2.me/theorems/834d7a63-7caa-4d6b-b1df-dd90fc990d87
-- title:
--   Godement Jacquet: algebra Map mem laurent Subalgebra
-- statement:
--   The Godement Jacquet construction uses the algebra Map mem laurent Subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJLaurentIdeal.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJLaurentIdeal.lean#L25-L33

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

theorem GroundTheory.Automorphic.GodementJacquet.algebraMap_mem_laurentSubalgebra (P : ℂ[X]) :
    algebraMap ℂ[X] (RatFunc ℂ) P ∈ laurentSubalgebra := by sorry
