-- Prove2me | Theorems.Thm_GlobalTheory_SmulIntegralDenominator_main
-- name    : GlobalTheory.SmulIntegralDenominator.main
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:47:49.185836+00:00
-- url     : https://prove2.me/theorems/13a763de-3b24-4894-ac61-b9014aa3c812
-- title:
--   Smul Integral Denominator: main
-- statement:
--   The Smul Integral Denominator construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsSmulIntegral.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsSmulIntegral.lean#L36-L39

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

theorem GlobalTheory.SmulIntegralDenominator.main : (let d1 : {K : Type} → [inst : Field K] → [inst_1 : ValuativeRel K] → [inst_2 : TopologicalSpace K] → {R : Type} → [inst_3 : CommRing R] → [inst_4 : Algebra K R] → [inst_5 : TopologicalSpace R] → Formalism.MainNotions.S.Loc.LocE K R → K → R → Prop := @(fun {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] {R : Type} [CommRing R] [Algebra K R] [TopologicalSpace R] (L : Formalism.MainNotions.S.Loc.LocE K R) (γ : K) (x : R) ↦ ∃ o ∈ Formalism.MainNotions.S.Loc.LocE.O L, x = (Algebra.algebraMap K R : K → R) γ * o); ∀ {K : Type} [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K] {R : Type} [inst_3 : CommRing R] [inst_4 : Algebra K R] [inst_5 : TopologicalSpace R] (L : Formalism.MainNotions.S.Loc.LocE K R) {ι : Type} [Fintype ι] (f : ι → R), ∃ e ∈ Valuation.integer (ValuativeRel.valuation K), e ≠ (0 : K) ∧ ∀ (i : ι), d1 L e⁻¹ (f i)) := by sorry
