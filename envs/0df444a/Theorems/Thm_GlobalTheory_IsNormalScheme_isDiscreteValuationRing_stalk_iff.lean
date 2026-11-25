-- Prove2me | Theorems.Thm_GlobalTheory_IsNormalScheme_isDiscreteValuationRing_stalk_iff
-- name    : GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:00.601434+00:00
-- url     : https://prove2.me/theorems/6c6e6a3e-52bb-49a2-bd6f-313b432bb9a7
-- title:
--   Is Normal Scheme: is Discrete Valuation Ring stalk iff
-- statement:
--   The Is Normal Scheme construction uses the is Discrete Valuation Ring stalk iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsOpenOfMemIrreducibleComponentsOfFinite.lean#L172-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsOpenOfMemIrreducibleComponentsOfFinite.lean#L172-L178

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIrreducibleGeneralizations
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
attribute [instance] IsNormalScheme.isDomain_stalk IsNormalScheme.isIntegrallyClosed_stalk
open GlobalTheory.IsNormalScheme

theorem GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk_iff {X : Scheme.{u}} [IsNormalScheme X]
    [IsLocallyNoetherian X] {x : X} :
    IsDiscreteValuationRing (X.presheaf.stalk x) ↔ Order.coheight x = 1 := by sorry
