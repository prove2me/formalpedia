-- Prove2me | Theorems.Thm_GlobalTheory_isIso_of_isClosedImmersion_of_schemeDominant
-- name    : GlobalTheory.isIso_of_isClosedImmersion_of_schemeDominant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:52.004401+00:00
-- url     : https://prove2.me/theorems/27f851ce-7603-4ae8-9e52-f457edc94e2c
-- title:
--   Global Theory: is Iso of is Closed Immersion of scheme Dominant
-- statement:
--   The Global Theory construction uses the is Iso of is Closed Immersion of scheme Dominant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L44-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
noncomputable section
variable {T' T P : Scheme.{u}}

theorem GlobalTheory.isIso_of_isClosedImmersion_of_schemeDominant (i : T ⟶ P) [IsClosedImmersion i]
    [IsSchemeTheoreticallyDominant i] : IsIso i := by sorry
