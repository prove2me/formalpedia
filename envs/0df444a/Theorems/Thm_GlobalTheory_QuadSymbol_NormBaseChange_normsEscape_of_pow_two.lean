-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_NormBaseChange_normsEscape_of_pow_two
-- name    : GlobalTheory.QuadSymbol.NormBaseChange.normsEscape_of_pow_two
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:12:28.147799+00:00
-- url     : https://prove2.me/theorems/3e5a1a0f-81c4-46cf-b348-9132c4f8136f
-- title:
--   Norm Base Change: norms Escape of pow two
-- statement:
--   The Norm Base Change construction uses the norms Escape of pow two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IndexTwoOfFiniteReal.lean#L241-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IndexTwoOfFiniteReal.lean#L241-L276

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
variable {A : Type} [Field A] [CharZero A]
  (hA : ∀ (B : Type) [Field B] [Algebra A B] [FiniteDimensional A B], IndexTwo B)
include hA

theorem GlobalTheory.QuadSymbol.NormBaseChange.normsEscape_of_pow_two (M : Type) [Field M] [Algebra A M] [FiniteDimensional A M]
    [IsGalois A M] : ∀ (m : ℕ) (K : IntermediateField A M) (n : ℕ), Module.finrank A K = m →
      Module.finrank K M = 2 ^ n → NormsEscape A K := by sorry
