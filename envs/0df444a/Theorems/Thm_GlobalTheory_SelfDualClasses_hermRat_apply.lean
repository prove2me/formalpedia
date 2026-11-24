-- Prove2me | Theorems.Thm_GlobalTheory_SelfDualClasses_hermRat_apply
-- name    : GlobalTheory.SelfDualClasses.hermRat_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:52:02.630057+00:00
-- url     : https://prove2.me/theorems/f9e4acbe-1532-4dfe-bb9f-1bee60ccbec0
-- title:
--   Self Dual Classes: herm Rat apply
-- statement:
--   The Self Dual Classes construction uses the herm Rat apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FiniteClassesSelfDualOfSelfDual.lean#L23-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FiniteClassesSelfDualOfSelfDual.lean#L23-L23

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

theorem GlobalTheory.SelfDualClasses.hermRat_apply {n : ℕ} (x y : Fin n → E) : hermRat n x y = herm 1 x y := by sorry
