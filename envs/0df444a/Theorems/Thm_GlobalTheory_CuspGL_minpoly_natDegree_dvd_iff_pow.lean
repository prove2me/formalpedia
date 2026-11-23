-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_minpoly_natDegree_dvd_iff_pow
-- name    : GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:54.983626+00:00
-- url     : https://prove2.me/theorems/333c61ee-6e7e-4bcf-a82e-b5efdd98f06f
-- title:
--   Cusp GL: minpoly nat Degree dvd iff pow
-- statement:
--   The Cusp GL construction uses the minpoly nat Degree dvd iff pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FrobeniusTorusMinpolyDegreeRootPowerSum.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FrobeniusTorusMinpolyDegreeRootPowerSum.lean#L14-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FrobeniusTorusMinpolyDegreeRootPowerSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F] [Finite F]
open Polynomial
variable {F : Type} [Field F] [Finite F]

theorem GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow (α : AlgebraicClosure F) (m : ℕ) :
    (minpoly F α).natDegree ∣ m ↔ α ^ Nat.card F ^ m = α := by sorry
