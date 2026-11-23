-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_MassMult_finite_end
-- name    : GlobalTheory.CuspGL.MassMult.finite_end
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:03.647534+00:00
-- url     : https://prove2.me/theorems/c81a0ff4-856c-407a-9e96-0a6151d7eded
-- title:
--   Mass Mult: finite end
-- statement:
--   The Mass Mult construction uses the finite end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EndomorphismMassMulParabolicInductionTrivial.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EndomorphismMassMulParabolicInductionTrivial.lean#L41-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumSubspaceStabilizerMulBlockFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesMulGeneralLinearGroupCardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassEqOfLinearEquivInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassMulParabolicInductionTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.MassMult

theorem GlobalTheory.CuspGL.MassMult.finite_end (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] : Finite (Module.End F V) := by sorry
