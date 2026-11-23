-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_MassMult_mass_eq
-- name    : GlobalTheory.CuspGL.MassMult.mass_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:20:52.396014+00:00
-- url     : https://prove2.me/theorems/67d46a2a-5c44-4a71-87bc-3595111ffcb0
-- title:
--   Mass Mult: mass eq
-- statement:
--   The Mass Mult construction uses the mass eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EndomorphismMassMulParabolicInductionTrivial.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EndomorphismMassMulParabolicInductionTrivial.lean#L24-L30

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
open Classical

theorem GlobalTheory.CuspGL.MassMult.mass_eq {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (φ : Module.End F V → ℂ) (P : F[X]) :
    mass φ P = ∑ᶠ g, if LinearMap.charpoly g = P then φ g else 0 := by sorry
