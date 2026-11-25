-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_index_comap_sUnitsToSIdeles
-- name    : GroundTheory.Global.IdeleGroup.index_comap_sUnitsToSIdeles
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:12:20.759797+00:00
-- url     : https://prove2.me/theorems/f198a0bb-be08-4205-978c-92b642e11b9f
-- title:
--   Idele Group: index comap s Units To SIdeles
-- statement:
--   The Idele Group construction uses the index comap s Units To SIdeles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IndexFormula.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IndexFormula.lean#L27-L29

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

theorem GroundTheory.Global.IdeleGroup.index_comap_sUnitsToSIdeles (W : Subgroup (sIdeles S)) :
    (W.comap (sUnitsToSIdeles S)).index = W.relIndex (sIdelesToIdeleClassGroup S).ker := by sorry
