-- Prove2me | Theorems.Thm_GlobalTheory_flat_of_schemeDominant_of_isBezout
-- name    : GlobalTheory.flat_of_schemeDominant_of_isBezout
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:45.200479+00:00
-- url     : https://prove2.me/theorems/c6b1c81b-4ded-4a91-ab99-a48adc74d8c8
-- title:
--   Global Theory: flat of scheme Dominant of is Bezout
-- statement:
--   The Global Theory construction uses the flat of scheme Dominant of is Bezout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L110-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L110-L114

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

theorem GlobalTheory.flat_of_schemeDominant_of_isBezout {O : CommRingCat.{u}} [IsDomain O] [IsBezout O]
    (d : T' ⟶ T) (s : T ⟶ Spec O) [IsSchemeTheoreticallyDominant d] [QuasiCompact d]
    [Flat (d ≫ s)] : Flat s := by sorry
