-- Prove2me | Theorems.Thm_GlobalTheory_T_heckeChar_uniformiser_value_isAlgebraic
-- name    : GlobalTheory.T.heckeChar_uniformiser_value_isAlgebraic
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:33:20.051194+00:00
-- url     : https://prove2.me/theorems/a56c7eae-6fbe-4107-b8a7-6610361066ad
-- title:
--   T: hecke Char uniformiser value is Algebraic
-- statement:
--   The T construction uses the hecke Char uniformiser value is Algebraic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HeckeCharUniformiserValueIsAlgebraicStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HeckeCharUniformiserValueIsAlgebraicStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeckeCharUniformiserValueIsAlgebraic
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_AlgValsFinMain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeckeCharUniformiserValueIsAlgebraicStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Host
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.heckeChar_uniformiser_value_isAlgebraic : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (m : (L →+* ℂ) → ℤ), (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ φ : L →+* ℂ, φ (k : L) ^ m φ) → ∀ w : HeightOneSpectrum (𝓞 L), IsAlgebraic ℚ ((χ.val w : ℂˣ) : ℂ) := by sorry
