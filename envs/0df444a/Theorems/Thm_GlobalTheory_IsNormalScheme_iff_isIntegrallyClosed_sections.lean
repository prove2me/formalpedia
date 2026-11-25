-- Prove2me | Theorems.Thm_GlobalTheory_IsNormalScheme_iff_isIntegrallyClosed_sections
-- name    : GlobalTheory.IsNormalScheme.iff_isIntegrallyClosed_sections
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:11.583679+00:00
-- url     : https://prove2.me/theorems/b2c81bd0-8bf1-44c5-b577-ece44ec51616
-- title:
--   Is Normal Scheme: iff is Integrally Closed sections
-- statement:
--   The Is Normal Scheme construction uses the iff is Integrally Closed sections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsOpenOfMemIrreducibleComponentsOfFinite.lean#L393-L395
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsOpenOfMemIrreducibleComponentsOfFinite.lean#L393-L395

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

theorem GlobalTheory.IsNormalScheme.iff_isIntegrallyClosed_sections (X : Scheme.{u}) [IsIntegral X] :
    IsNormalScheme X ↔ ∀ (U : X.Opens) [Nonempty U], IsIntegrallyClosed Γ(X, U) := by sorry
