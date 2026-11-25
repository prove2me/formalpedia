-- Prove2me | Theorems.Thm_GroundTheory_LocalField_lowerRamificationGroup_map_restrictScalars
-- name    : GroundTheory.LocalField.lowerRamificationGroup_map_restrictScalars
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:50:57.380216+00:00
-- url     : https://prove2.me/theorems/53e8962e-0216-404d-a3f8-aa9b0b8987c5
-- title:
--   Local Field: lower Ramification Group map restrict Scalars
-- statement:
--   The Local Field construction uses the lower Ramification Group map restrict Scalars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndex.lean#L142-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndex.lean#L142-L146

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
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
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing IsDiscreteValuationRing Polynomial
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
variable (M : IntermediateField K L)

theorem GroundTheory.LocalField.lowerRamificationGroup_map_restrictScalars (i : ℤ) :
    (lowerRamificationGroup M L i).map (AlgEquiv.restrictScalarsHom K) =
      lowerRamificationGroup K L i ⊓ M.fixingSubgroup := by sorry
