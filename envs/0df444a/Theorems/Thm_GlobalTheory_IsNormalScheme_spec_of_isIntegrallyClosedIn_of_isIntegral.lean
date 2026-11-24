-- Prove2me | Theorems.Thm_GlobalTheory_IsNormalScheme_spec_of_isIntegrallyClosedIn_of_isIntegral
-- name    : GlobalTheory.IsNormalScheme.spec_of_isIntegrallyClosedIn_of_isIntegral
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:12:27.394808+00:00
-- url     : https://prove2.me/theorems/1a996290-0647-4e87-bb86-b88bc102cad0
-- title:
--   Is Normal Scheme: spec of is Integrally Closed In of is Integral
-- statement:
--   The Is Normal Scheme construction uses the spec of is Integrally Closed In of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsOpenOfMemIrreducibleComponentsOfFinite.lean#L573-L589
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsOpenOfMemIrreducibleComponentsOfFinite.lean#L573-L589

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

theorem GlobalTheory.IsNormalScheme.spec_of_isIntegrallyClosedIn_of_isIntegral {X : Scheme.{u}} [IsNormalScheme X]
    [IsIntegral X] (U : X.Opens) (A : Type u) [CommRing A] [Algebra A Γ(X, U)]
    [IsIntegrallyClosedIn A Γ(X, U)] : IsNormalScheme (Spec (.of A)) := by sorry
