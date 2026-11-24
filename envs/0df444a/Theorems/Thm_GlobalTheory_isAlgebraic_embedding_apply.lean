-- Prove2me | Theorems.Thm_GlobalTheory_isAlgebraic_embedding_apply
-- name    : GlobalTheory.isAlgebraic_embedding_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:56:43.818515+00:00
-- url     : https://prove2.me/theorems/8db3c50c-01dc-4041-994b-48c872ece53a
-- title:
--   Global Theory: is Algebraic embedding apply
-- statement:
--   The Global Theory construction uses the is Algebraic embedding apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HeckeCharUniformiserValueIsAlgebraic.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HeckeCharUniformiserValueIsAlgebraic.lean#L11-L13

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

theorem GlobalTheory.isAlgebraic_embedding_apply {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) (x : L) :
    IsAlgebraic ℚ (φ x) := by sorry
