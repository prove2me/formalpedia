-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspLabel_exists_cuspidal_label
-- name    : GlobalTheory.CompanionTheory.TyFin.CuspLabel.exists_cuspidal_label
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:46:47.941374+00:00
-- url     : https://prove2.me/theorems/37da58a7-e5ee-42ac-b858-ad80b2d2ec91
-- title:
--   Cusp Label: exists cuspidal label
-- statement:
--   The Cusp Label construction uses the exists cuspidal label property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCuspidalWithLabel.lean#L57-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCuspidalWithLabel.lean#L57-L134

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_CharacterEqOfRepIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalOfUnipotentSumsVanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MatrixTraceIffIsCharacterOverSubfieldComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterCuspidalRootSumRegularStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_GeneralLinearFunctionExtendZeroEndPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExponentRegularOfNatDegreeMinpolyGeneratorPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumUnipotentRadicalEqZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyOfIrreduciStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharacterAdditiveAndXSubOnePowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FrobeniusTorusMinpolyDegreeRootPowerSumStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCuspidalWithLabel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.CuspLabel

theorem GlobalTheory.CompanionTheory.TyFin.CuspLabel.exists_cuspidal_label : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K) (d : ℕ), 1 ≤ d → ∀ P : K[X], P.Monic → Irreducible P → P ≠ X → P.natDegree = d →
    ∃ τ : FDRep ℂ (GL (Fin d) K), Simple τ ∧ IsCuspidal K τ ∧ HasCuspLabel C τ P := by sorry
