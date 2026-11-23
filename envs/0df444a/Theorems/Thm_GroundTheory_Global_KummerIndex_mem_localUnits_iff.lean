-- Prove2me | Theorems.Thm_GroundTheory_Global_KummerIndex_mem_localUnits_iff
-- name    : GroundTheory.Global.KummerIndex.mem_localUnits_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:39.453045+00:00
-- url     : https://prove2.me/theorems/2c649e4e-ebb8-4538-b953-0f6c9d4f4939
-- title:
--   Kummer Index: mem local Units iff
-- statement:
--   The Kummer Index construction uses the mem local Units iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/KummerIndexLemma/HasEnoughRootsOfUnityOfRingHom.lean#L26-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/KummerIndexLemma/HasEnoughRootsOfUnityOfRingHom.lean#L26-L37

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
variable {v}

theorem GroundTheory.Global.KummerIndex.mem_localUnits_iff {x : (v.adicCompletion K)ˣ} :
    x ∈ localUnits v ↔ Valued.v (x : v.adicCompletion K) = 1 := by sorry
