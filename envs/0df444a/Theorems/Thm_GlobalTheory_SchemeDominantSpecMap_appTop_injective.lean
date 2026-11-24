-- Prove2me | Theorems.Thm_GlobalTheory_SchemeDominantSpecMap_appTop_injective
-- name    : GlobalTheory.SchemeDominantSpecMap.appTop_injective
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:47:43.198267+00:00
-- url     : https://prove2.me/theorems/d4f90cd4-fa23-491a-b5b6-db0b4d79da54
-- title:
--   Scheme Dominant Spec Map: app Top injective
-- statement:
--   The Scheme Dominant Spec Map construction uses the app Top injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsSchemeTheoreticallyDominantSpecMap.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsSchemeTheoreticallyDominantSpecMap.lean#L9-L16

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

theorem GlobalTheory.SchemeDominantSpecMap.appTop_injective {R A : CommRingCat.{u_1}} (φ : R ⟶ A) (h : Function.Injective φ) :
    Function.Injective (Spec.map φ).appTop := by sorry
