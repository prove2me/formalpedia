-- Prove2me | Theorems.Thm_GroundTheory_Global_KummerIndex_index_unitsPow
-- name    : GroundTheory.Global.KummerIndex.index_unitsPow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:41:04.992581+00:00
-- url     : https://prove2.me/theorems/9872a20e-c483-4348-a373-afc89ed92fd9
-- title:
--   Kummer Index: index units Pow
-- statement:
--   The Kummer Index construction uses the index units Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/KummerIndexLemma/HasEnoughRootsOfUnityOfRingHom.lean#L137-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/KummerIndexLemma/HasEnoughRootsOfUnityOfRingHom.lean#L137-L143

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexProductFormula
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_KummerIndexLemma_HasEnoughRootsOfUnityOfRingHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField GroundTheory.ProfCoh WithZero
open GroundTheory.Global.KummerIndex
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem GroundTheory.Global.KummerIndex.index_unitsPow (p : ℕ) [NeZero p] [HasEnoughRootsOfUnity K p]
    (hv : (p : 𝓞 K) ∉ v.asIdeal) :
    (unitsPow (v.adicCompletion K) p).index = p ^ 2 := by sorry
