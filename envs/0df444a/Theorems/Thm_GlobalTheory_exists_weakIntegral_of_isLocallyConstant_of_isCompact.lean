-- Prove2me | Theorems.Thm_GlobalTheory_exists_weakIntegral_of_isLocallyConstant_of_isCompact
-- name    : GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:49.403801+00:00
-- url     : https://prove2.me/theorems/446317ad-b230-434a-b944-70251d4bf6b3
-- title:
--   Global Theory: exists weak Integral of is Locally Constant of is Compact
-- statement:
--   The Global Theory construction uses the exists weak Integral of is Locally Constant of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsWeakIntegralOfIsLocallyConstantOfIsCompact.lean#L9-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsWeakIntegralOfIsLocallyConstantOfIsCompact.lean#L9-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsWeakIntegralOfIsLocallyConstantOfIsCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory
open MeasureTheory ValuativeRel Matrix

theorem GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact :
    ∀ (U : Type) [TopologicalSpace U] [T2Space U] [MeasurableSpace U] [OpensMeasurableSpace U] (m : Measure U) [IsFiniteMeasureOnCompacts m] (V : Type) [AddCommGroup V] [Module ℂ V] (T : U → V) (_ : IsLocallyConstant T) (K : Set U) (_ : IsCompact K) (_ : ∀ u, u ∉ K → T u = 0), ∃ w : V, ∀ l : V →ₗ[ℂ] ℂ, l w = ∫ u, l (T u) ∂m := by sorry
