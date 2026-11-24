-- Prove2me | Theorems.Thm_GlobalTheory_IsNormalScheme_isIntegral_of_connectedSpace
-- name    : GlobalTheory.IsNormalScheme.isIntegral_of_connectedSpace
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:12:56.311908+00:00
-- url     : https://prove2.me/theorems/d42eff20-f054-4b57-9183-eb2ecdef3806
-- title:
--   Is Normal Scheme: is Integral of connected Space
-- statement:
--   The Is Normal Scheme construction uses the is Integral of connected Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsOpenOfMemIrreducibleComponentsOfFinite.lean#L250-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsOpenOfMemIrreducibleComponentsOfFinite.lean#L250-L257

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

theorem GlobalTheory.IsNormalScheme.isIntegral_of_connectedSpace (X : Scheme.{u}) [IsNormalScheme X] [IsLocallyNoetherian X]
    [ConnectedSpace X] : IsIntegral X := by sorry
