-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_apply_eq_of_mem_lowerRamificationGroup_zero
-- name    : GroundTheory.ProfCoh.apply_eq_of_mem_lowerRamificationGroup_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:48:29.488245+00:00
-- url     : https://prove2.me/theorems/a095df05-e7f7-4786-b1fb-c8fd68d0a028
-- title:
--   Prof Coh: apply eq of mem lower Ramification Group zero
-- statement:
--   The Prof Coh construction uses the apply eq of mem lower Ramification Group zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L322-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L322-L332

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.LocalField ValuativeRel IntermediateField
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}

theorem GroundTheory.ProfCoh.apply_eq_of_mem_lowerRamificationGroup_zero {m : ℕ} (hm : (m : 𝓀[L]) ≠ 0)
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ lowerRamificationGroup K L 0) {ζ : L} (hζ : ζ ^ m = 1) :
    σ ζ = ζ := by sorry
