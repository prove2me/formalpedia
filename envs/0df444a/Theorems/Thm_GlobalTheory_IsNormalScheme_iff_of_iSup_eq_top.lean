-- Prove2me | Theorems.Thm_GlobalTheory_IsNormalScheme_iff_of_iSup_eq_top
-- name    : GlobalTheory.IsNormalScheme.iff_of_iSup_eq_top
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:13:18.632799+00:00
-- url     : https://prove2.me/theorems/cd042f51-4e65-4a0d-afc3-27c557784fa7
-- title:
--   Is Normal Scheme: iff of i Sup eq top
-- statement:
--   The Is Normal Scheme construction uses the iff of i Sup eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsOpenOfMemIrreducibleComponentsOfFinite.lean#L95-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsOpenOfMemIrreducibleComponentsOfFinite.lean#L95-L100

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

theorem GlobalTheory.IsNormalScheme.iff_of_iSup_eq_top {X : Scheme.{u}} {ι : Sort*} (U : ι → X.Opens) (hU : iSup U = ⊤) :
    IsNormalScheme X ↔ ∀ i, IsNormalScheme (U i) := by sorry
