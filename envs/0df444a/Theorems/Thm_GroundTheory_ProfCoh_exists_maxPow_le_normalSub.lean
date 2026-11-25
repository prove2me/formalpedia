-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_exists_maxPow_le_normalSub
-- name    : GroundTheory.ProfCoh.exists_maxPow_le_normalSub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:51:46.80249+00:00
-- url     : https://prove2.me/theorems/2a88fbdf-3bfd-4ca1-a308-bae19a2a21bf
-- title:
--   Prof Coh: exists max Pow le normal Sub
-- statement:
--   The Prof Coh construction uses the exists max Pow le normal Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L323-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L323-L337

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10

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
universe u
open GroundTheory.LocalField ValuativeRel IsLocalRing
variable {E F : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F]
variable {l : ℕ} [NeZero l] (d : AdditiveFunction.{u} l (F ≃ₐ[E] F))
attribute [local instance] integerAction unitFiltrationAction
attribute [local instance] maxPowAction normalSubAction

theorem GroundTheory.ProfCoh.exists_maxPow_le_normalSub [IsGalois E F] {θ : F}
    (hθ : LinearIndependent E fun σ : F ≃ₐ[E] F ↦ σ θ) :
    ∃ j, ∀ k ≥ j, maxPow F k ≤ normalSub E θ := by sorry
