-- Prove2me | Theorems.Thm_GlobalTheory_heckeChar_val_isAlgebraic
-- name    : GlobalTheory.heckeChar_val_isAlgebraic
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:55:55.153128+00:00
-- url     : https://prove2.me/theorems/3fa42a50-3028-4c1f-9cdd-4450d99c420d
-- title:
--   Global Theory: hecke Char val is Algebraic
-- statement:
--   The Global Theory construction uses the hecke Char val is Algebraic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HeckeCharUniformiserValueIsAlgebraic.lean#L15-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HeckeCharUniformiserValueIsAlgebraic.lean#L15-L73

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_AlgValsFinMain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeckeCharUniformiserValueIsAlgebraic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Host
noncomputable section
open GlobalTheory
open PI.AlgValsFin.W ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1

theorem GlobalTheory.heckeChar_val_isAlgebraic : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (m : (L →+* ℂ) → ℤ),
    (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ φ : L →+* ℂ, φ (k : L) ^ m φ) →
    ∀ w : HeightOneSpectrum (𝓞 L), IsAlgebraic ℚ ((χ.val w : ℂˣ) : ℂ) := by sorry
