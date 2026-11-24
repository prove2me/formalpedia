-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteLevel_antitone
-- name    : GroundTheory.Global.IdeleGroup.finiteLevel_antitone
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:39:28.888905+00:00
-- url     : https://prove2.me/theorems/005688c5-e42a-4a04-b8d4-ba45e351873e
-- title:
--   Idele Group: finite Level antitone
-- statement:
--   The Idele Group construction uses the finite Level antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Conductor.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Conductor.lean#L58-L60

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

theorem GroundTheory.Global.IdeleGroup.finiteLevel_antitone {m n : HeightOneSpectrum (𝓞 K) → ℕ} (h : m ≤ n) :
    finiteLevel n ≤ finiteLevel m := by sorry
