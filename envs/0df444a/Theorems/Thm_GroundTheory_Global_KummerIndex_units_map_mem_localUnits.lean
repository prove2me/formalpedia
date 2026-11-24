-- Prove2me | Theorems.Thm_GroundTheory_Global_KummerIndex_units_map_mem_localUnits
-- name    : GroundTheory.Global.KummerIndex.units_map_mem_localUnits
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:40:19.543434+00:00
-- url     : https://prove2.me/theorems/48acab5f-fcd8-4923-994f-5f61dbe13cb8
-- title:
--   Kummer Index: units map mem local Units
-- statement:
--   The Kummer Index construction uses the units map mem local Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/KummerIndexLemma/HasEnoughRootsOfUnityOfRingHom.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/KummerIndexLemma/HasEnoughRootsOfUnityOfRingHom.lean#L39-L43

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

theorem GroundTheory.Global.KummerIndex.units_map_mem_localUnits {a : Kˣ} (ha : v.valuation K (a : K) = 1) :
    Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) a ∈ localUnits v := by sorry
