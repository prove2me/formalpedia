-- Prove2me | Theorems.Thm_GlobalTheory_SelfDualClasses_finite_linearMap
-- name    : GlobalTheory.SelfDualClasses.finite_linearMap
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:52:08.406722+00:00
-- url     : https://prove2.me/theorems/63d50d8a-aa6c-4d67-9bbe-21863855c3ec
-- title:
--   Self Dual Classes: finite linear Map
-- statement:
--   The Self Dual Classes construction uses the finite linear Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FiniteClassesSelfDualOfSelfDual.lean#L99-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FiniteClassesSelfDualOfSelfDual.lean#L99-L105

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClassesSelfDualOfSelfDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD Module Submodule
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory.SelfDualClasses
open ShortVectors

theorem GlobalTheory.SelfDualClasses.finite_linearMap {R M T : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup T] [Module R T] [Module.Finite R M] [Finite T] : Finite (M →ₗ[R] T) := by sorry
