-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_eq_zero_of_mass_charpoly_eq_zero
-- name    : GlobalTheory.CuspGL.eq_zero_of_mass_charpoly_eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:34:11.158082+00:00
-- url     : https://prove2.me/theorems/432e4e91-3c36-4d69-86c0-a244d314e53e
-- title:
--   Cusp GL: eq zero of mass charpoly eq zero
-- statement:
--   The Cusp GL construction uses the eq zero of mass charpoly eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/PrimitiveEndClassFunctionZeroOfCharpolyMassZero.lean#L24-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/PrimitiveEndClassFunctionZeroOfCharpolyMassZero.lean#L24-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveEqPolynomialVonMangoldtConvolutionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ConjOfPrimaryFinrankKerPowEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveEqPolynomialVonMangoldtConvolutionOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ConjOfPrimaryFinrankKerPowEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassMobiusInverseMonicEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveEndClassFunctionEqZeroOfPrimaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveEndClassFunctionZeroOfCharpolyMassZero
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

theorem GlobalTheory.CuspGL.eq_zero_of_mass_charpoly_eq_zero (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ) (hc : IsClassFn φ) (hp : IsPrimitive φ)
    (g : Module.End F V) (hm : mass φ (LinearMap.charpoly g) = 0) : φ g = 0 := by sorry
