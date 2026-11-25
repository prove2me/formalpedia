-- Prove2me | Theorems.Thm_GroundTheory_LocalField_natCast_ramificationIndex_ne_zero
-- name    : GroundTheory.LocalField.natCast_ramificationIndex_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:15:07.865863+00:00
-- url     : https://prove2.me/theorems/61c03560-ec22-5229-9f29-7fc82c23f1d4
-- title:
--   Local Field: nat Cast ramification Index ne zero
-- statement:
--   The Local Field construction uses the nat Cast ramification Index ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationTame.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationTame.lean#L21-L27

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_RamificationTame
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
open scoped IntermediateField
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing IsDiscreteValuationRing
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem GroundTheory.LocalField.natCast_ramificationIndex_ne_zero
    (he : Nat.Coprime (ramificationIndex K L) (ringChar 𝓀[K])) :
    (ramificationIndex K L : 𝓀[L]) ≠ 0 := by sorry
