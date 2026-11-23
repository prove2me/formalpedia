-- Prove2me | Theorems.Thm_GlobalTheory_SchemeDominantSpecMap_isSchemeTheoreticallyDominant_specMap
-- name    : GlobalTheory.SchemeDominantSpecMap.isSchemeTheoreticallyDominant_specMap
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:52:08.496138+00:00
-- url     : https://prove2.me/theorems/48805be7-7822-4a4b-afde-50efe2626df3
-- title:
--   Scheme Dominant Spec Map: is Scheme Theoretically Dominant spec Map
-- statement:
--   The Scheme Dominant Spec Map construction uses the is Scheme Theoretically Dominant spec Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsSchemeTheoreticallyDominantSpecMap.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsSchemeTheoreticallyDominantSpecMap.lean#L18-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.SchemeDominantSpecMap

theorem GlobalTheory.SchemeDominantSpecMap.isSchemeTheoreticallyDominant_specMap {R A : CommRingCat.{u_1}} (φ : R ⟶ A)
    (h : Function.Injective φ) : IsSchemeTheoreticallyDominant (Spec.map φ) := by sorry
