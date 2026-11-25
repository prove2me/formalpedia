-- Prove2me | Theorems.Thm_GlobalTheory_SmulIntegralDenominator_exists_smul_integral
-- name    : GlobalTheory.SmulIntegralDenominator.exists_smul_integral
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:47:24.274799+00:00
-- url     : https://prove2.me/theorems/96adfbb6-76e6-56e4-be15-0c7f0be1e3be
-- title:
--   Smul Integral Denominator: exists smul integral
-- statement:
--   The Smul Integral Denominator construction uses the exists smul integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsSmulIntegral.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsSmulIntegral.lean#L12-L17

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsSmulIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel
open GlobalTheory GlobalTheory.SmulIntegralDenominator

theorem GlobalTheory.SmulIntegralDenominator.exists_smul_integral {K : Type} [Field K] [ValuativeRel K]
    {R : Type} [CommRing R] [Algebra K R] [Module.Finite K R] (x : R) :
    ∃ e : 𝒪[K], e ≠ 0 ∧ IsIntegral 𝒪[K] (e • x) := by sorry
