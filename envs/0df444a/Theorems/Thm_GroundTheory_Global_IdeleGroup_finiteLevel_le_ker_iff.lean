-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteLevel_le_ker_iff
-- name    : GroundTheory.Global.IdeleGroup.finiteLevel_le_ker_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:45.935612+00:00
-- url     : https://prove2.me/theorems/4da03a2e-62ae-4e13-9fdc-27f3ba4c5144
-- title:
--   Idele Group: finite Level le ker iff
-- statement:
--   The Idele Group construction uses the finite Level le ker iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Conductor.lean#L182-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Conductor.lean#L182-L217

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LocalConductor
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Conductor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Global
noncomputable section
open GroundTheory.Global.IdeleGroup
variable {K : Type*} [Field K] [NumberField K]
variable {H : Type*} [Group H] [TopologicalSpace H]

theorem GroundTheory.Global.IdeleGroup.finiteLevel_le_ker_iff (hH : NoSmallSubgroups H) (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H)
    (hχ : Continuous χ) (n : HeightOneSpectrum (𝓞 K) → ℕ) :
    finiteLevel n ≤ χ.ker ↔ ∀ v, conductorExponentAt χ v ≤ n v := by sorry
