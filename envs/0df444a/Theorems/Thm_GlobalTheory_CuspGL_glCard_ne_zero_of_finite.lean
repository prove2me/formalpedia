-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_glCard_ne_zero_of_finite
-- name    : GlobalTheory.CuspGL.glCard_ne_zero_of_finite
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:33:34.253258+00:00
-- url     : https://prove2.me/theorems/d141474a-ed00-482b-a0a4-f8108e2c6f1c
-- title:
--   Cusp GL: gl Card ne zero of finite
-- statement:
--   The Cusp GL construction uses the gl Card ne zero of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CharpolyEndomorphismDensityGLRecursion.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CharpolyEndomorphismDensityGLRecursion.lean#L33-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassMulParabolicInductionTrivialStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumCardCyclicVectorsInvariantSubspacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassOfCharpolyCardCyclicVectorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyEndomorphismDensityGLRecursion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL

theorem GlobalTheory.CuspGL.glCard_ne_zero_of_finite (F : Type) [Field F] [Finite F] (n : ℕ) : glCard F n ≠ 0 := by sorry
