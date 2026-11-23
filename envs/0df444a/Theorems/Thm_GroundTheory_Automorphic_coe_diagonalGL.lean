-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_coe_diagonalGL
-- name    : GroundTheory.Automorphic.coe_diagonalGL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:31.609075+00:00
-- url     : https://prove2.me/theorems/a2dd093a-d60b-4f2d-acca-a898569adc1e
-- title:
--   Automorphic: coe diagonal GL
-- statement:
--   The Automorphic construction uses the coe diagonal GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StrongApproximationSLElementary.lean#L83-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StrongApproximationSLElementary.lean#L83-L84

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

theorem GroundTheory.Automorphic.coe_diagonalGL (d : n → Rˣ) :
    (diagonalGL d : Matrix n n R) = diagonal fun k => (d k : R) := by sorry

attribute [defeq] GroundTheory.Automorphic.coe_diagonalGL
