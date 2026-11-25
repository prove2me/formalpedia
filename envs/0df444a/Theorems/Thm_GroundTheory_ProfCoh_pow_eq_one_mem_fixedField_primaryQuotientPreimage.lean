-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_pow_eq_one_mem_fixedField_primaryQuotientPreimage
-- name    : GroundTheory.ProfCoh.pow_eq_one_mem_fixedField_primaryQuotientPreimage
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:02:18.134522+00:00
-- url     : https://prove2.me/theorems/1a874410-382e-5198-8ad1-6f66c6640574
-- title:
--   Prof Coh: pow eq one mem fixed Field primary Quotient Preimage
-- statement:
--   The Prof Coh construction uses the pow eq one mem fixed Field primary Quotient Preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L389-L401
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L389-L401

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

theorem GroundTheory.ProfCoh.pow_eq_one_mem_fixedField_primaryQuotientPreimage {l : ℕ} (hl : l.Prime)
    (hlp : l ≠ ringChar 𝓀[K]) {ζ : L} (hζ : ζ ^ l = 1) :
    ζ ∈ fixedField (primaryQuotientPreimage (lowerRamificationGroup K L 0) l) := by sorry
