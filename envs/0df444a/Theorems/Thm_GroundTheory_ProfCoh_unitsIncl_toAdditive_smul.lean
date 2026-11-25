-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_unitsIncl_toAdditive_smul
-- name    : GroundTheory.ProfCoh.unitsIncl_toAdditive_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:52:55.222814+00:00
-- url     : https://prove2.me/theorems/b7ba0ea9-74a8-4fd1-879b-2e09dc78d6e5
-- title:
--   Prof Coh: units Incl to Additive smul
-- statement:
--   The Prof Coh construction uses the units Incl to Additive smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L275-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L275-L277

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
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

theorem GroundTheory.ProfCoh.unitsIncl_toAdditive_smul (σ : F ≃ₐ[E] F) (a : Additive 𝒪[F]ˣ) :
    (unitsIncl F).toAdditive (σ • a) = σ • (unitsIncl F).toAdditive a := by sorry
