-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_isOpen_finiteLevel
-- name    : GroundTheory.Global.IdeleGroup.isOpen_finiteLevel
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:35.622339+00:00
-- url     : https://prove2.me/theorems/53a2bff1-506b-481d-a34c-0c6325b62694
-- title:
--   Idele Group: is Open finite Level
-- statement:
--   The Idele Group construction uses the is Open finite Level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Conductor.lean#L93-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Conductor.lean#L93-L109

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

theorem GroundTheory.Global.IdeleGroup.isOpen_finiteLevel {n : HeightOneSpectrum (𝓞 K) → ℕ} (hn : (support n).Finite) :
    IsOpen (finiteLevel n : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := by sorry
