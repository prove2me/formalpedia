-- Prove2me | Theorems.Thm_GroundTheory_Global_natCard_residueField_adicCompletion
-- name    : GroundTheory.Global.natCard_residueField_adicCompletion
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:41:54.00018+00:00
-- url     : https://prove2.me/theorems/bd1f6043-5aad-4e75-82ff-69d605b367e7
-- title:
--   Global: nat Card residue Field adic Completion
-- statement:
--   The Global construction uses the nat Card residue Field adic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndexAtPlace.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndexAtPlace.lean#L37-L41

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
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
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  GroundTheory.LocalField
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem GroundTheory.Global.natCard_residueField_adicCompletion :
    Nat.card 𝓀[v.adicCompletion K] = Ideal.absNorm v.asIdeal := by sorry
