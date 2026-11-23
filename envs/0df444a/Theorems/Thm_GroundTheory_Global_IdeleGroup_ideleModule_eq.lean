-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_ideleModule_eq
-- name    : GroundTheory.Global.IdeleGroup.ideleModule_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:15:56.433985+00:00
-- url     : https://prove2.me/theorems/436d8559-db17-459b-8d50-35194e122433
-- title:
--   Idele Group: idele Module eq
-- statement:
--   The Idele Group construction uses the idele Module eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms.lean#L102-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms.lean#L102-L105

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable {K}

theorem GroundTheory.Global.IdeleGroup.ideleModule_eq (x : IdeleGroup K) :
    (ideleModule K x : ℝ) = (∏ w : InfinitePlace K, ‖(x : 𝔸[K]).1 w‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(x : 𝔸[K]).2 v‖ := by sorry
