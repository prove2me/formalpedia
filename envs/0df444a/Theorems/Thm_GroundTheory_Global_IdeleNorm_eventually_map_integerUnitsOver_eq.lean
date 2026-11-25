-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleNorm_eventually_map_integerUnitsOver_eq
-- name    : GroundTheory.Global.IdeleNorm.eventually_map_integerUnitsOver_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:09:56.049872+00:00
-- url     : https://prove2.me/theorems/7a252462-5737-56c8-a4ff-74f58dba59d9
-- title:
--   Idele Norm: eventually map integer Units Over eq
-- statement:
--   The Idele Norm construction uses the eventually map integer Units Over eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNormsEverywhere.lean#L47-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNormsEverywhere.lean#L47-L54

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNormGroups
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNormsEverywhere
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
open IsDedekindDomain NumberField Filter
open AdeleBaseChange SemiLocal
noncomputable section
open GroundTheory.Global.IdeleNorm
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
variable (L)

theorem GroundTheory.Global.IdeleNorm.eventually_map_integerUnitsOver_eq :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite,
      (integerUnitsOver L v).map (finiteLocalNorm L v) =
        (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by sorry
