-- Prove2me | Theorems.Thm_GlobalTheory_IsNormalScheme_connectedComponent_eq_irreducibleComponent
-- name    : GlobalTheory.IsNormalScheme.connectedComponent_eq_irreducibleComponent
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:12:24.540472+00:00
-- url     : https://prove2.me/theorems/16bb0e5e-df90-4c38-a534-62995a928938
-- title:
--   Is Normal Scheme: connected Component eq irreducible Component
-- statement:
--   The Is Normal Scheme construction uses the connected Component eq irreducible Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsOpenOfMemIrreducibleComponentsOfFinite.lean#L244-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsOpenOfMemIrreducibleComponentsOfFinite.lean#L244-L248

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

theorem GlobalTheory.IsNormalScheme.connectedComponent_eq_irreducibleComponent {X : Scheme.{u}} [IsNormalScheme X]
    [IsLocallyNoetherian X] (x : X) : connectedComponent x = irreducibleComponent x := by sorry
