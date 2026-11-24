-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_NormBaseChange_exists_sqrt_basis
-- name    : GlobalTheory.QuadSymbol.NormBaseChange.exists_sqrt_basis
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:39:34.653583+00:00
-- url     : https://prove2.me/theorems/dcb3ea9b-a973-4787-9f0b-fa5a36c05b6e
-- title:
--   Norm Base Change: exists sqrt basis
-- statement:
--   The Norm Base Change construction uses the exists sqrt basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IndexTwoOfFiniteReal.lean#L177-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IndexTwoOfFiniteReal.lean#L177-L191

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsKum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CyclicKummerNormFixedHilbert90
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HerbrandPrimeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PIdxUnitsFiniteExtensionAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSubgroupIndexTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndexTwoOfFiniteReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.QuadSymbol
open GlobalTheory.QuadSymbol.NormBaseChange
open NormIndex
variable {A B C : Type} [Field A] [Field B] [Field C]

theorem GlobalTheory.QuadSymbol.NormBaseChange.exists_sqrt_basis (A B : Type) [Field A] [Field B] [CharZero A] [Algebra A B]
    (hr : Module.finrank A B = 2) : ∃ (δ : A) (e : Module.Basis (Fin 2) A B),
      ¬ IsSquare δ ∧ e 0 = 1 ∧ e 1 * e 1 = algebraMap A B δ := by sorry
