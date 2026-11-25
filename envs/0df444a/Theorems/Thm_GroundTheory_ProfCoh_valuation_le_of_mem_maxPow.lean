-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_valuation_le_of_mem_maxPow
-- name    : GroundTheory.ProfCoh.valuation_le_of_mem_maxPow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:51:50.343097+00:00
-- url     : https://prove2.me/theorems/a892d56c-e8c7-4dcc-bc6d-d86fc27f987f
-- title:
--   Prof Coh: valuation le of mem max Pow
-- statement:
--   The Prof Coh construction uses the valuation le of mem max Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L317-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L317-L321

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
omit [FiniteDimensional E F]

theorem GroundTheory.ProfCoh.valuation_le_of_mem_maxPow {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {k : ℕ} {x : 𝒪[F]}
    (hx : x ∈ 𝓂[F] ^ k) : valuation F (x : F) ≤ valuation F (ϖ : F) ^ k := by sorry
