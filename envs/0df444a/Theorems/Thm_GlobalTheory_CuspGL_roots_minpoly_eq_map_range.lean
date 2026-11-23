-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_roots_minpoly_eq_map_range
-- name    : GlobalTheory.CuspGL.roots_minpoly_eq_map_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:43.965801+00:00
-- url     : https://prove2.me/theorems/bbb0b96a-2897-4db3-a8b0-fbbb1745ea39
-- title:
--   Cusp GL: roots minpoly eq map range
-- statement:
--   The Cusp GL construction uses the roots minpoly eq map range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FrobeniusTorusMinpolyDegreeRootPowerSum.lean#L33-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FrobeniusTorusMinpolyDegreeRootPowerSum.lean#L33-L73

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

theorem GlobalTheory.CuspGL.roots_minpoly_eq_map_range (α : AlgebraicClosure F) :
    ((minpoly F α).map (algebraMap F (AlgebraicClosure F))).roots =
      (Multiset.range (minpoly F α).natDegree).map fun i => α ^ Nat.card F ^ i := by sorry
