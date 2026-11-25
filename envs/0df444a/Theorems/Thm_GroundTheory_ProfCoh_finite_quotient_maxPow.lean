-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_finite_quotient_maxPow
-- name    : GroundTheory.ProfCoh.finite_quotient_maxPow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:51:44.415855+00:00
-- url     : https://prove2.me/theorems/02654e76-f54f-4d81-b591-30fdbac83e6d
-- title:
--   Prof Coh: finite quotient max Pow
-- statement:
--   The Prof Coh construction uses the finite quotient max Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L342-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L342-L358

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
omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension E F]
  [FiniteDimensional E F]

theorem GroundTheory.ProfCoh.finite_quotient_maxPow {θ : F} {k : ℕ} (hle : maxPow F k ≤ normalSub E θ) :
    Finite (normalSub E θ ⧸ (AddSubgroup.inclusion hle).range) := by sorry
