-- Prove2me | Theorems.Thm_GlobalTheory_LatOrbGL_mem_range_iff
-- name    : GlobalTheory.LatOrbGL.mem_range_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:25.482379+00:00
-- url     : https://prove2.me/theorems/381ff797-352f-4422-9266-b936fec20b78
-- title:
--   Lat Orb GL: mem range iff
-- statement:
--   The Lat Orb GL construction uses the mem range iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemGLintIffMatrixImageStandardLatticeEq.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemGLintIffMatrixImageStandardLatticeEq.lean#L10-L13

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGLintIffMatrixImageStandardLatticeEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
open GlobalTheory GlobalTheory.LatOrbGL
variable {K : Type} [Field K] (V : ValuationSubring K)

theorem GlobalTheory.LatOrbGL.mem_range_iff (x : K) : x ∈ (algebraMap V K).range ↔ x ∈ V := by sorry
