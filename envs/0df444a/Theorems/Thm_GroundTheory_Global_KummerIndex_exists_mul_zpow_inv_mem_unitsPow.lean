-- Prove2me | Theorems.Thm_GroundTheory_Global_KummerIndex_exists_mul_zpow_inv_mem_unitsPow
-- name    : GroundTheory.Global.KummerIndex.exists_mul_zpow_inv_mem_unitsPow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:55:52.974521+00:00
-- url     : https://prove2.me/theorems/3ed79399-06ff-4b81-b24f-951d59eeced6
-- title:
--   Kummer Index: exists mul zpow inv mem units Pow
-- statement:
--   The Kummer Index construction uses the exists mul zpow inv mem units Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/KummerIndexLemma/HasEnoughRootsOfUnityOfRingHom.lean#L157-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/KummerIndexLemma/HasEnoughRootsOfUnityOfRingHom.lean#L157-L178

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

theorem GroundTheory.Global.KummerIndex.exists_mul_zpow_inv_mem_unitsPow (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity K p]
    (hv : (p : 𝓞 K) ∉ v.asIdeal) {a x : (v.adicCompletion K)ˣ} (ha : a ∈ localUnits v)
    (hx : x ∈ localUnits v) (hap : a ∉ unitsPow (v.adicCompletion K) p) :
    ∃ k : ℤ, x * (a ^ k)⁻¹ ∈ unitsPow (v.adicCompletion K) p := by sorry
