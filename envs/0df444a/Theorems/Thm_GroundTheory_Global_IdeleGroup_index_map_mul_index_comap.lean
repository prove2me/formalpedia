-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_index_map_mul_index_comap
-- name    : GroundTheory.Global.IdeleGroup.index_map_mul_index_comap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:00:10.609325+00:00
-- url     : https://prove2.me/theorems/92a0fff1-a003-4cfb-9989-61821407f0cf
-- title:
--   Idele Group: index map mul index comap
-- statement:
--   The Idele Group construction uses the index map mul index comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IndexFormula.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IndexFormula.lean#L31-L36

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleGroups
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexFormula
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
open NumberField IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable (S : Set (HeightOneSpectrum (𝓞 K)))

theorem GroundTheory.Global.IdeleGroup.index_map_mul_index_comap (h : (diagonal K).range ⊔ sIdeles S = ⊤)
    (W : Subgroup (sIdeles S)) :
    (W.map (sIdelesToIdeleClassGroup S)).index * (W.comap (sUnitsToSIdeles S)).index =
      W.index := by sorry
