-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteLevel_le_finiteLevel_zero
-- name    : GroundTheory.Global.IdeleGroup.finiteLevel_le_finiteLevel_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:26.632242+00:00
-- url     : https://prove2.me/theorems/1931eb12-519d-42de-9c6c-e9a075bb56f9
-- title:
--   Idele Group: finite Level le finite Level zero
-- statement:
--   The Idele Group construction uses the finite Level le finite Level zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Conductor.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Conductor.lean#L62-L64

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

theorem GroundTheory.Global.IdeleGroup.finiteLevel_le_finiteLevel_zero (n : HeightOneSpectrum (𝓞 K) → ℕ) :
    finiteLevel n ≤ finiteLevel 0 := by sorry
