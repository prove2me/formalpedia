-- Prove2me | Theorems.Thm_GlobalTheory_IsNormalScheme_of_isIntegral_of_isIntegrallyClosed
-- name    : GlobalTheory.IsNormalScheme.of_isIntegral_of_isIntegrallyClosed
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:12:03.639832+00:00
-- url     : https://prove2.me/theorems/4a8ae980-3bea-4023-9de0-dd1a8bdfaac0
-- title:
--   Is Normal Scheme: of is Integral of is Integrally Closed
-- statement:
--   The Is Normal Scheme construction uses the of is Integral of is Integrally Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsOpenOfMemIrreducibleComponentsOfFinite.lean#L148-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsOpenOfMemIrreducibleComponentsOfFinite.lean#L148-L156

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

theorem GlobalTheory.IsNormalScheme.of_isIntegral_of_isIntegrallyClosed (X : Scheme.{u}) [IsIntegral X]
    (h : ∀ (U : X.Opens) [Nonempty U], IsAffineOpen U → IsIntegrallyClosed Γ(X, U)) :
    IsNormalScheme X := by sorry
