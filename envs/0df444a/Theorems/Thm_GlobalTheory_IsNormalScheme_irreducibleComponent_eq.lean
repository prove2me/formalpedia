-- Prove2me | Theorems.Thm_GlobalTheory_IsNormalScheme_irreducibleComponent_eq
-- name    : GlobalTheory.IsNormalScheme.irreducibleComponent_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:04.390008+00:00
-- url     : https://prove2.me/theorems/0d3af50f-40a3-4da6-b4e7-8f014f2b5705
-- title:
--   Is Normal Scheme: irreducible Component eq
-- statement:
--   The Is Normal Scheme construction uses the irreducible Component eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsOpenOfMemIrreducibleComponentsOfFinite.lean#L201-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsOpenOfMemIrreducibleComponentsOfFinite.lean#L201-L204

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

theorem GlobalTheory.IsNormalScheme.irreducibleComponent_eq {X : Scheme.{u}} [IsNormalScheme X] {x : X} {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hx : x ∈ Z) : irreducibleComponent x = Z := by sorry
