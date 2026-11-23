-- Prove2me | Theorems.Thm_GlobalTheory_mono_specMap_localization
-- name    : GlobalTheory.mono_specMap_localization
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:38.745259+00:00
-- url     : https://prove2.me/theorems/8fd98eea-5cce-48e1-953f-6311f1cd3680
-- title:
--   Global Theory: mono spec Map localization
-- statement:
--   The Global Theory construction uses the mono spec Map localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L122-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L122-L126

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

theorem GlobalTheory.mono_specMap_localization {O : Type u} [CommRing O] (M : Submonoid O) (K : Type u)
    [CommRing K] [Algebra O K] [IsLocalization M K] :
    Mono (Spec.map (CommRingCat.ofHom (algebraMap O K))) := by sorry
