-- Prove2me | Theorems.Thm_GlobalTheory_IsNormalScheme_normalization_of_isIntegral
-- name    : GlobalTheory.IsNormalScheme.normalization_of_isIntegral
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:12:16.61659+00:00
-- url     : https://prove2.me/theorems/4dd889b8-76c1-5957-b6d1-42a4352d9543
-- title:
--   Is Normal Scheme: normalization of is Integral
-- statement:
--   The Is Normal Scheme construction uses the normalization of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsOpenOfMemIrreducibleComponentsOfFinite.lean#L598-L603
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsOpenOfMemIrreducibleComponentsOfFinite.lean#L598-L603

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

theorem GlobalTheory.IsNormalScheme.normalization_of_isIntegral {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] [IsNormalScheme X] [IsIntegral X] : IsNormalScheme f.normalization := by sorry
