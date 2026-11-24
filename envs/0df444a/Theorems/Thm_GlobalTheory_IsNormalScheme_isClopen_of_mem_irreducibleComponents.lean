-- Prove2me | Theorems.Thm_GlobalTheory_IsNormalScheme_isClopen_of_mem_irreducibleComponents
-- name    : GlobalTheory.IsNormalScheme.isClopen_of_mem_irreducibleComponents
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:12:20.021592+00:00
-- url     : https://prove2.me/theorems/ba04e3b6-9d12-48be-934b-b52608d86f5a
-- title:
--   Is Normal Scheme: is Clopen of mem irreducible Components
-- statement:
--   The Is Normal Scheme construction uses the is Clopen of mem irreducible Components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsOpenOfMemIrreducibleComponentsOfFinite.lean#L240-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsOpenOfMemIrreducibleComponentsOfFinite.lean#L240-L242

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

theorem GlobalTheory.IsNormalScheme.isClopen_of_mem_irreducibleComponents {X : Scheme.{u}} [IsNormalScheme X]
    [IsLocallyNoetherian X] {Z : Set X} (hZ : Z ∈ irreducibleComponents X) : IsClopen Z := by sorry
