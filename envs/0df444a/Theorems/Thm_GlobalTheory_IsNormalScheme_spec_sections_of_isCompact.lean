-- Prove2me | Theorems.Thm_GlobalTheory_IsNormalScheme_spec_sections_of_isCompact
-- name    : GlobalTheory.IsNormalScheme.spec_sections_of_isCompact
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:06.155521+00:00
-- url     : https://prove2.me/theorems/0229f47e-adc0-4743-9ed3-5c69e24cbe03
-- title:
--   Is Normal Scheme: spec sections of is Compact
-- statement:
--   The Is Normal Scheme construction uses the spec sections of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsOpenOfMemIrreducibleComponentsOfFinite.lean#L569-L571
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsOpenOfMemIrreducibleComponentsOfFinite.lean#L569-L571

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

theorem GlobalTheory.IsNormalScheme.spec_sections_of_isCompact {X : Scheme.{u}} [IsNormalScheme X] [IsLocallyNoetherian X]
    {U : X.Opens} (hU : IsCompact (U : Set X)) : IsNormalScheme (Spec Γ(X, U)) := by sorry
